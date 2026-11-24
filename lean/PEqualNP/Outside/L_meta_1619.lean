import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1619

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stp w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stp]
    omega

lemma fold_getD (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stp w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (stp w g) i (by simp [stp]; omega)]
    exact List.getD_append w _ false i hi

lemma wire_gate_aux (pre post : List Gate) (g : Gate) (x : List Bool) :
    ((pre ++ g :: post).foldl stp x).getD (x.length + pre.length) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + pre.length then
          ((pre ++ g :: post).foldl stp x).getD i false else false) := by
  rw [List.foldl_append, List.foldl_cons]
  have hwl : (pre.foldl stp x).length = x.length + pre.length := fold_len pre x
  generalize pre.foldl stp x = w at hwl ⊢
  have hsl : (stp w g).length = w.length + 1 := by simp [stp]
  rw [fold_getD post (stp w g) (x.length + pre.length) (by omega)]
  have h1 : (stp w g).getD (x.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    rw [← hwl]
    unfold stp
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + pre.length
  · rw [if_pos hi, fold_getD post (stp w g) i (by omega)]
    exact (List.getD_append w _ false i (by omega)).symm
  · rw [if_neg hi]
    exact List.getD_eq_default _ _ (by omega)

lemma wire_gate (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl stp x).getD (x.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < x.length + k then (gs.foldl stp x).getD i false else false) := by
  have hsplit : gs.take k ++ gs[k] :: gs.drop (k + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hlen : (gs.take k).length = k := by
    rw [List.length_take]; omega
  have h := wire_gate_aux (gs.take k) (gs.drop (k + 1)) gs[k] x
  rw [hsplit, hlen] at h
  exact h

def val (gates : List Gate) (u : Fin 13) (w : ℕ) : Bool :=
  (gates.foldl stp (List.ofFn fun j : Fin 13 => decide (j = u))).getD w false

lemma val_input (gates : List Gate) (u : Fin 13) (w : ℕ) (hw : w < 13) :
    val gates u w = decide ((⟨w, hw⟩ : Fin 13) = u) := by
  unfold val
  rw [fold_getD gates _ w (by rw [List.length_ofFn]; exact hw)]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hw)]
  simp only [List.getElem_ofFn]

lemma val_gate (gates : List Gate) (u : Fin 13) (k : ℕ) (hk : k < gates.length) :
    val gates u (13 + k) = (gates[k]).op.eval ((gates[k]).inputs.map fun i =>
      if i < 13 + k then val gates u i else false) := by
  have h := wire_gate gates (List.ofFn fun j : Fin 13 => decide (j = u)) k hk
  rw [List.length_ofFn] at h
  exact h

lemma val_big (gates : List Gate) (u : Fin 13) (w : ℕ) (hw : 13 + gates.length ≤ w) :
    val gates u w = false := by
  unfold val
  apply List.getD_eq_default
  rw [fold_len, List.length_ofFn]
  exact hw

def SS (gates : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun u => val gates u w = true)

def Ch {n : ℕ} (Sg : Fin n → Finset (Fin 13)) (k : Fin n) (X : Finset (Fin 13)) : Prop :=
  X.card ≤ 1 ∨ ∃ k' : Fin n, k' < k ∧ X = Sg k'

def Cs (gates : List Gate) (k i : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun u => (if i < 13 + k then val gates u i else false) = true)

lemma ch_cs (gates : List Gate) (k : Fin gates.length) (i : ℕ) :
    Ch (fun j : Fin gates.length => SS gates (13 + j.val)) k (Cs gates k.val i) := by
  by_cases h1 : i < 13 + k.val
  · by_cases h2 : i < 13
    · left
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Cs, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1,
        val_input gates _ i h2, decide_eq_true_eq] at ha hb
      rw [← ha, ← hb]
    · right
      refine ⟨⟨i - 13, by omega⟩, ?_, ?_⟩
      · rw [Fin.lt_def]
        show i - 13 < k.val
        omega
      · have h3 : 13 + (i - 13) = i := by omega
        show Cs gates k.val i = SS gates (13 + (i - 13))
        rw [h3]
        ext u
        simp only [Cs, SS, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
  · left
    have h3 : Cs gates k.val i = ∅ := by
      ext u
      simp [Cs, h1]
    rw [h3]
    simp

lemma gate_cases (gates : List Gate)
    (hfan : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : Fin gates.length) :
    SS gates (13 + k.val) = Finset.univ ∨ SS gates (13 + k.val) = ∅ ∨
      ∃ X Y, Ch (fun j : Fin gates.length => SS gates (13 + j.val)) k X ∧
        Ch (fun j : Fin gates.length => SS gates (13 + j.val)) k Y ∧
        (SS gates (13 + k.val) = X ∩ Y ∨ SS gates (13 + k.val) = X ∪ Y) := by
  have hv : ∀ u, val gates u (13 + k.val) = (gates[k.val]).op.eval
      ((gates[k.val]).inputs.map fun i => if i < 13 + k.val then val gates u i else false) :=
    fun u => val_gate gates u k.val k.isLt
  have hf := hfan (gates[k.val]) (List.getElem_mem k.isLt)
  obtain ⟨g, hg⟩ : ∃ g, g = gates[k.val] := ⟨_, rfl⟩
  rw [← hg] at hv hf
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hf
  simp only at hv hop hlen
  rcases inputs with _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · left
      ext u
      simp [SS, hv u, GateOp.eval]
    · right; left
      ext u
      simp [SS, hv u, GateOp.eval]
  · right; right
    refine ⟨Cs gates k.val c, Cs gates k.val c, ch_cs gates k c, ch_cs gates k c, Or.inl ?_⟩
    rcases hop with rfl | rfl
    · ext u
      simp [SS, Cs, hv u, GateOp.eval]
    · ext u
      simp [SS, Cs, hv u, GateOp.eval]
  · right; right
    refine ⟨Cs gates k.val c, Cs gates k.val d, ch_cs gates k c, ch_cs gates k d, ?_⟩
    rcases hop with rfl | rfl
    · left
      ext u
      simp [SS, Cs, hv u, GateOp.eval]
    · right
      ext u
      simp [SS, Cs, hv u, GateOp.eval]
  · exfalso
    simp at hlen

section
variable {n : ℕ} (Sg : Fin n → Finset (Fin 13)) (L : Fin 13 → Finset (Fin 13))

def PP (l : Fin 13) : Finset (Fin n) :=
  Finset.univ.filter (fun k => 2 ≤ (Sg k).card ∧ Sg k ⊆ L l)

def TT : Finset (Fin n) :=
  Finset.univ.filter (fun k => (∀ l, ¬ Sg k ⊆ L l) ∧ Sg k ≠ Finset.univ)

def UU : Finset (Fin n) :=
  Finset.univ.filter (fun k => Sg k = Finset.univ)

lemma mem_PP (l : Fin 13) (k : Fin n) :
    k ∈ PP Sg L l ↔ 2 ≤ (Sg k).card ∧ Sg k ⊆ L l := by
  simp [PP]

lemma mem_TT (k : Fin n) :
    k ∈ TT Sg L ↔ (∀ l, ¬ Sg k ⊆ L l) ∧ Sg k ≠ Finset.univ := by
  simp [TT]

lemma mem_UU (k : Fin n) : k ∈ UU Sg ↔ Sg k = Finset.univ := by
  simp [UU]

lemma mem_PP_line (hL4 : ∀ l, (L l).card = 4) (l : Fin 13) (g : Fin n) (hg : Sg g = L l) :
    g ∈ PP Sg L l := by
  rw [mem_PP, hg, hL4]
  exact ⟨by norm_num, Finset.Subset.refl _⟩

lemma key (hL4 : ∀ l, (L l).card = 4)
    (hLu : ∀ (A : Finset (Fin 13)) (l l' : Fin 13), 2 ≤ A.card → A ⊆ L l → A ⊆ L l' → l = l')
    (hgate : ∀ k : Fin n, Sg k = Finset.univ ∨ Sg k = ∅ ∨
      ∃ X Y, Ch Sg k X ∧ Ch Sg k Y ∧ (Sg k = X ∩ Y ∨ Sg k = X ∪ Y))
    (k : Fin n) (l : Fin 13) (hk : Sg k = L l) :
    (∃ k', k' < k ∧ k' ∈ PP Sg L l) ∨
    (∃ a b, a < k ∧ a ∈ TT Sg L ∧ b ∈ TT Sg L ∧ a ≠ b ∧ Sg a ∩ Sg b = L l) := by
  have hbig : ∀ X, Ch Sg k X → 2 ≤ X.card → ∃ k', k' < k ∧ X = Sg k' := by
    intro X hX h2
    rcases hX with h | h
    · omega
    · exact h
  have h4 := hL4 l
  rcases hgate k with h | h | ⟨X, Y, hX, hY, h | h⟩
  · exfalso
    rw [← hk, h, Finset.card_univ, Fintype.card_fin] at h4
    omega
  · exfalso
    rw [← hk, h, Finset.card_empty] at h4
    omega
  · rw [hk] at h
    have hlX : L l ⊆ X := by rw [h]; exact Finset.inter_subset_left
    have hlY : L l ⊆ Y := by rw [h]; exact Finset.inter_subset_right
    have cX := Finset.card_le_card hlX
    have cY := Finset.card_le_card hlY
    obtain ⟨a, ha, rfl⟩ := hbig X hX (by omega)
    obtain ⟨b, hb, rfl⟩ := hbig Y hY (by omega)
    by_cases hal : Sg a = L l
    · left
      exact ⟨a, ha, mem_PP_line Sg L hL4 l a hal⟩
    by_cases hbl : Sg b = L l
    · left
      exact ⟨b, hb, mem_PP_line Sg L hL4 l b hbl⟩
    right
    have key1 : ∀ c : Fin n, L l ⊆ Sg c → Sg c ≠ L l → ∀ l', ¬ Sg c ⊆ L l' := by
      intro c hc hne l' hl'
      have hll : l = l' :=
        hLu (L l) l l' (by omega) (Finset.Subset.refl _) (hc.trans hl')
      subst hll
      exact hne (Finset.Subset.antisymm hl' hc)
    refine ⟨a, b, ha, (mem_TT Sg L a).mpr ⟨key1 a hlX hal, ?_⟩,
      (mem_TT Sg L b).mpr ⟨key1 b hlY hbl, ?_⟩, ?_, h.symm⟩
    · intro hu
      rw [hu, Finset.univ_inter] at h
      exact hbl h.symm
    · intro hu
      rw [hu, Finset.inter_univ] at h
      exact hal h.symm
    · intro hab
      rw [hab, Finset.inter_self] at h
      exact hbl h.symm
  · rw [hk] at h
    have hc : 4 ≤ X.card + Y.card := by
      have h5 := Finset.card_union_le X Y
      rw [← h, hL4] at h5
      exact h5
    have hXs : X ⊆ L l := by rw [h]; exact Finset.subset_union_left
    have hYs : Y ⊆ L l := by rw [h]; exact Finset.subset_union_right
    left
    by_cases hx : 2 ≤ X.card
    · obtain ⟨a, ha, rfl⟩ := hbig X hX hx
      exact ⟨a, ha, (mem_PP Sg L l a).mpr ⟨hx, hXs⟩⟩
    · have hy : 2 ≤ Y.card := by omega
      obtain ⟨b, hb, rfl⟩ := hbig Y hY hy
      exact ⟨b, hb, (mem_PP Sg L l b).mpr ⟨hy, hYs⟩⟩

lemma pairs (hL4 : ∀ l, (L l).card = 4)
    (hLu : ∀ (A : Finset (Fin 13)) (l l' : Fin 13), 2 ≤ A.card → A ⊆ L l → A ⊆ L l' → l = l')
    (hgate : ∀ k : Fin n, Sg k = Finset.univ ∨ Sg k = ∅ ∨
      ∃ X Y, Ch Sg k X ∧ Ch Sg k Y ∧ (Sg k = X ∩ Y ∨ Sg k = X ∪ Y))
    (l : Fin 13) (g : Fin n) (hg : Sg g = L l) (h1 : (PP Sg L l).card ≤ 1) :
    ∃ a b, a < g ∧ a ∈ TT Sg L ∧ b ∈ TT Sg L ∧ a ≠ b ∧ Sg a ∩ Sg b = L l := by
  rcases key Sg L hL4 hLu hgate g l hg with ⟨k', hk', hk'P⟩ | h
  · exfalso
    have hgP : g ∈ PP Sg L l := mem_PP_line Sg L hL4 l g hg
    have h2 := Finset.card_le_one.mp h1 k' hk'P g hgP
    exact absurd h2 (ne_of_lt hk')
  · exact h

lemma special (hL4 : ∀ l, (L l).card = 4)
    (hLu : ∀ (A : Finset (Fin 13)) (l l' : Fin 13), 2 ≤ A.card → A ⊆ L l → A ⊆ L l' → l = l')
    (hLe : ∀ A : Finset (Fin 13), A.card ≤ 2 → ∃ l, A ⊆ L l)
    (hgate : ∀ k : Fin n, Sg k = Finset.univ ∨ Sg k = ∅ ∨
      ∃ X Y, Ch Sg k X ∧ Ch Sg k Y ∧ (Sg k = X ∩ Y ∨ Sg k = X ∪ Y))
    (hall : ∀ l, (∃ g, Sg g = L l) ∧ (PP Sg L l).card ≤ 1) (hU : UU Sg = ∅) : False := by
  have hT : ∀ m : ℕ, ∀ a : Fin n, a.val < m → a ∉ TT Sg L := by
    intro m
    induction m with
    | zero => intro a ha; omega
    | succ m ih =>
      intro a ha haT
      have hmin : ∀ k', k' < a → k' ∉ TT Sg L := fun k' hk' =>
        ih k' (by rw [Fin.lt_def] at hk'; omega)
      have haT' := (mem_TT Sg L a).mp haT
      have hch : ∀ X, Ch Sg a X → X.card ≤ 1 := by
        intro X hX
        rcases hX with h | ⟨k', hk', rfl⟩
        · exact h
        · by_contra hcard
          have hk'T := hmin k' hk'
          have hnu : Sg k' ≠ Finset.univ := by
            intro hu
            have h3 : k' ∈ UU Sg := (mem_UU Sg k').mpr hu
            rw [hU] at h3
            simp at h3
          have hex : ∃ l', Sg k' ⊆ L l' := by
            by_contra hno
            exact hk'T ((mem_TT Sg L k').mpr ⟨not_exists.mp hno, hnu⟩)
          obtain ⟨l', hl'⟩ := hex
          obtain ⟨⟨g, hg⟩, h1⟩ := hall l'
          have hkP : k' ∈ PP Sg L l' := (mem_PP Sg L l' k').mpr ⟨by omega, hl'⟩
          have hgP : g ∈ PP Sg L l' := mem_PP_line Sg L hL4 l' g hg
          have hgk : g = k' := Finset.card_le_one.mp h1 g hgP k' hkP
          subst hgk
          obtain ⟨a', b', ha', ha'T, _⟩ := pairs Sg L hL4 hLu hgate l' g hg h1
          exact hmin a' (lt_trans ha' hk') ha'T
      have hcard : (Sg a).card ≤ 2 := by
        rcases hgate a with h | h | ⟨X, Y, hX, hY, h | h⟩
        · exact absurd h haT'.2
        · rw [h]; simp
        · rw [h]
          have h5 := Finset.card_le_card (Finset.inter_subset_left : X ∩ Y ⊆ X)
          have h6 := hch X hX
          omega
        · rw [h]
          have h5 := Finset.card_union_le X Y
          have h6 := hch X hX
          have h7 := hch Y hY
          omega
      obtain ⟨l, hl⟩ := hLe (Sg a) hcard
      exact haT'.1 l hl
  obtain ⟨⟨g, hg⟩, h1⟩ := hall 0
  obtain ⟨a, b, ha, haT, _⟩ := pairs Sg L hL4 hLu hgate 0 g hg h1
  exact hT (a.val + 1) a (by omega) haT

lemma count (hL4 : ∀ l, (L l).card = 4)
    (hLu : ∀ (A : Finset (Fin 13)) (l l' : Fin 13), 2 ≤ A.card → A ⊆ L l → A ⊆ L l' → l = l')
    (hLe : ∀ A : Finset (Fin 13), A.card ≤ 2 → ∃ l, A ⊆ L l)
    (hgate : ∀ k : Fin n, Sg k = Finset.univ ∨ Sg k = ∅ ∨
      ∃ X Y, Ch Sg k X ∧ Ch Sg k Y ∧ (Sg k = X ∩ Y ∨ Sg k = X ∪ Y))
    (B : Finset (Fin 13)) (H : Finset (Fin n))
    (hout : ∀ l ∈ B, ∃ k : Fin n, Sg k = L l)
    (hH : ∀ k ∈ H, 2 ≤ (Sg k).card ∧ ∃ l, l ∉ B ∧ Sg k ⊆ L l) :
    3 * B.card + 2 * H.card ≤ 2 * n := by
  have hUL : ∀ k l, Sg k = Finset.univ → ¬ Sg k ⊆ L l := by
    intro k l hk hs
    have h5 := Finset.card_le_card hs
    rw [hk, Finset.card_univ, Fintype.card_fin, hL4] at h5
    omega
  have dHT : Disjoint H (TT Sg L) := by
    rw [Finset.disjoint_left]
    intro k hk hkT
    obtain ⟨_, l, _, hl⟩ := hH k hk
    exact ((mem_TT Sg L k).mp hkT).1 l hl
  have dHU : Disjoint H (UU Sg) := by
    rw [Finset.disjoint_left]
    intro k hk hkU
    obtain ⟨_, l, _, hl⟩ := hH k hk
    exact hUL k l ((mem_UU Sg k).mp hkU) hl
  have dTU : Disjoint (TT Sg L) (UU Sg) := by
    rw [Finset.disjoint_left]
    intro k hkT hkU
    exact ((mem_TT Sg L k).mp hkT).2 ((mem_UU Sg k).mp hkU)
  have dP : Disjoint (H ∪ TT Sg L ∪ UU Sg) (B.biUnion (PP Sg L)) := by
    rw [Finset.disjoint_left]
    intro k hk hkP
    rw [Finset.mem_biUnion] at hkP
    obtain ⟨l, hlB, hkl⟩ := hkP
    obtain ⟨h2, hsub⟩ := (mem_PP Sg L l k).mp hkl
    rw [Finset.mem_union, Finset.mem_union] at hk
    rcases hk with (hk | hk) | hk
    · obtain ⟨_, l', hl'B, hl'⟩ := hH k hk
      have hll := hLu (Sg k) l l' h2 hsub hl'
      subst hll
      exact hl'B hlB
    · exact ((mem_TT Sg L k).mp hk).1 l hsub
    · exact hUL k l ((mem_UU Sg k).mp hk) hsub
  have dPP : (B : Set (Fin 13)).PairwiseDisjoint (PP Sg L) := by
    intro l _ l' _ hne
    show Disjoint (PP Sg L l) (PP Sg L l')
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨h2, hsub⟩ := (mem_PP Sg L l k).mp hk
    obtain ⟨_, hsub'⟩ := (mem_PP Sg L l' k).mp hk'
    exact hne (hLu (Sg k) l l' h2 hsub hsub')
  have hcount : H.card + (TT Sg L).card + (UU Sg).card + ∑ l ∈ B, (PP Sg L l).card ≤ n := by
    have h := Finset.card_le_univ (H ∪ TT Sg L ∪ UU Sg ∪ B.biUnion (PP Sg L))
    rw [Finset.card_union_of_disjoint dP,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dHU, dTU⟩),
      Finset.card_union_of_disjoint dHT, Finset.card_biUnion dPP, Fintype.card_fin] at h
    exact h
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = B.filter (fun l => (PP Sg L l).card ≤ 1) := ⟨_, rfl⟩
  have hmemB1 : ∀ l, l ∈ B1 → l ∈ B ∧ (PP Sg L l).card ≤ 1 := by
    intro l hl
    rw [hB1, Finset.mem_filter] at hl
    exact hl
  have hsum : 2 * B.card ≤ ∑ l ∈ B, (PP Sg L l).card + B1.card := by
    rw [hB1, Finset.card_filter, ← Finset.sum_add_distrib]
    have h5 : ∀ l ∈ B, 2 ≤ (PP Sg L l).card + (if (PP Sg L l).card ≤ 1 then 1 else 0) := by
      intro l hl
      obtain ⟨g, hg⟩ := hout l hl
      have hgP : g ∈ PP Sg L l := mem_PP_line Sg L hL4 l g hg
      have h6 : 1 ≤ (PP Sg L l).card := Finset.card_pos.mpr ⟨g, hgP⟩
      split_ifs <;> omega
    calc 2 * B.card = ∑ l ∈ B, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum h5
  have hpair : B1.card * 2 ≤ (TT Sg L).offDiag.card * 1 := by
    apply Finset.card_mul_le_card_mul
      (fun (l : Fin 13) (p : Fin n × Fin n) => Sg p.1 ∩ Sg p.2 = L l)
    · intro l hl
      obtain ⟨hlB, hl1⟩ := hmemB1 l hl
      obtain ⟨g, hg⟩ := hout l hlB
      obtain ⟨a, b, _, haT, hbT, hab, hI⟩ := pairs Sg L hL4 hLu hgate l g hg hl1
      have h5 : 1 < (Finset.bipartiteAbove
          (fun (l : Fin 13) (p : Fin n × Fin n) => Sg p.1 ∩ Sg p.2 = L l)
          (TT Sg L).offDiag l).card := by
        rw [Finset.one_lt_card]
        refine ⟨(a, b), ?_, (b, a), ?_, ?_⟩
        · rw [Finset.mem_bipartiteAbove, Finset.mem_offDiag]
          exact ⟨⟨haT, hbT, hab⟩, hI⟩
        · rw [Finset.mem_bipartiteAbove, Finset.mem_offDiag]
          refine ⟨⟨hbT, haT, hab.symm⟩, ?_⟩
          show Sg b ∩ Sg a = L l
          rw [Finset.inter_comm]
          exact hI
        · intro h6
          exact hab (Prod.ext_iff.mp h6).1
      exact h5
    · intro p _
      rw [Finset.card_le_one]
      intro l hl l' hl'
      rw [Finset.mem_bipartiteBelow] at hl hl'
      have e1 : Sg p.1 ∩ Sg p.2 = L l := hl.2
      have e2 : Sg p.1 ∩ Sg p.2 = L l' := hl'.2
      have h4 := hL4 l
      exact hLu (L l) l l' (by omega) (Finset.Subset.refl _) (by rw [← e1, e2])
  have hspec : B1.card ≤ 12 ∨ 1 ≤ (UU Sg).card := by
    by_contra hcon
    have hB13 : B1.card ≤ 13 := by
      have h5 := Finset.card_le_univ B1
      rwa [Fintype.card_fin] at h5
    have hU0 : UU Sg = ∅ := Finset.card_eq_zero.mp (by omega)
    have hB1u : B1 = Finset.univ :=
      Finset.eq_univ_of_card B1 (by rw [Fintype.card_fin]; omega)
    apply special Sg L hL4 hLu hLe hgate _ hU0
    intro l
    have hl : l ∈ B1 := by rw [hB1u]; exact Finset.mem_univ l
    obtain ⟨hlB, hl1⟩ := hmemB1 l hl
    exact ⟨hout l hlB, hl1⟩
  have hB1le : B1.card ≤ B.card := by
    rw [hB1]
    exact Finset.card_filter_le _ _
  have hB13 : B.card ≤ 13 := by
    have h5 := Finset.card_le_univ B
    rwa [Fintype.card_fin] at h5
  rw [Finset.offDiag_card] at hpair
  generalize (TT Sg L).card = t at hpair hcount
  generalize (UU Sg).card = u at hspec hcount
  generalize ∑ l ∈ B, (PP Sg L l).card = s at hsum hcount
  generalize B1.card = b1 at hsum hpair hspec hB1le
  generalize B.card = b at hsum hB1le hB13 ⊢
  generalize H.card = h at hcount ⊢
  by_cases ht : 7 ≤ t
  · clear hpair
    omega
  · have ht' : t ≤ 6 := by omega
    interval_cases t <;> omega

end

theorem main_aux : ∀ (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ l0 : Fin 13, (Finset.univ.filter (fun p0 : Fin 13 => I p0 l0)).card = 4) → (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (l2 u2 : Fin 13), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin 13 => decide (u2k = u2)))).getD (out l2) false = true ↔ I u2 l2) → ∀ (B : Finset (Fin 13)) (H : Finset (Fin gates.length)), (∀ k5 ∈ H, 2 ≤ (Finset.univ.filter (fun u5 : Fin 13 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin 13 => decide (u5k = u5)))).getD (13 + k5.val) false = true)).card ∧ ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u6 : Fin 13, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin 13 => decide (u6k = u6)))).getD (13 + k5.val) false = true → I u6 l4) → 3 * B.card + 2 * H.card ≤ 2 * gates.length := by
  intro I _ gates out hI4 hIu hfan hout B H hH
  have hLu : ∀ (A : Finset (Fin 13)) (l l' : Fin 13), 2 ≤ A.card →
      A ⊆ Finset.univ.filter (fun p => I p l) →
      A ⊆ Finset.univ.filter (fun p => I p l') → l = l' := by
    intro A l l' hA h1 h2
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hA
    have a1 := (Finset.mem_filter.mp (h1 hp)).2
    have a2 := (Finset.mem_filter.mp (h1 hq)).2
    have b1 := (Finset.mem_filter.mp (h2 hp)).2
    have b2 := (Finset.mem_filter.mp (h2 hq)).2
    exact (hIu p q hpq).unique ⟨a1, a2⟩ ⟨b1, b2⟩
  have hLe : ∀ A : Finset (Fin 13), A.card ≤ 2 →
      ∃ l, A ⊆ Finset.univ.filter (fun p => I p l) := by
    intro A hA
    have hsub : ∃ p q : Fin 13, p ≠ q ∧ A ⊆ {p, q} := by
      rcases Nat.lt_or_ge A.card 2 with h | h
      · rcases Nat.lt_or_ge A.card 1 with h0 | h1
        · have h3 : A = ∅ := Finset.card_eq_zero.mp (by omega)
          exact ⟨0, 1, by decide, by rw [h3]; exact Finset.empty_subset _⟩
        · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (by omega : A.card = 1)
          obtain ⟨q, hq⟩ := exists_ne p
          exact ⟨p, q, hq.symm, by rw [hp]; simp⟩
      · obtain ⟨p, q, hpq, hA'⟩ := Finset.card_eq_two.mp (by omega : A.card = 2)
        exact ⟨p, q, hpq, by rw [hA']⟩
    obtain ⟨p, q, hpq, hA'⟩ := hsub
    obtain ⟨l, ⟨h1, h2⟩, _⟩ := hIu p q hpq
    refine ⟨l, fun x hx => ?_⟩
    have h3 := hA' hx
    rw [Finset.mem_insert, Finset.mem_singleton] at h3
    rcases h3 with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
  have hout1 : ∀ l u, val gates u (out l) = true ↔ I u l := hout
  have hSout : ∀ l, SS gates (out l) = Finset.univ.filter (fun p => I p l) := by
    intro l
    ext u
    simp only [SS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hout1 l u
  have hout2 : ∀ l ∈ B, ∃ k : Fin gates.length,
      SS gates (13 + k.val) = Finset.univ.filter (fun p => I p l) := by
    intro l _
    by_cases h1 : out l < 13
    · exfalso
      have hc : (SS gates (out l)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [SS, Finset.mem_filter, Finset.mem_univ, true_and,
          val_input gates _ (out l) h1, decide_eq_true_eq] at ha hb
        rw [← ha, ← hb]
      rw [hSout l, hI4 l] at hc
      omega
    · by_cases h2 : 13 + gates.length ≤ out l
      · exfalso
        have hc : SS gates (out l) = ∅ := by
          ext u
          simp [SS, val_big gates u (out l) h2]
        have h4 := hI4 l
        rw [← hSout l, hc] at h4
        simp at h4
      · refine ⟨⟨out l - 13, by omega⟩, ?_⟩
        have h3 : 13 + (out l - 13) = out l := by omega
        show SS gates (13 + (out l - 13)) = _
        rw [h3]
        exact hSout l
  have hH1 : ∀ k ∈ H, 2 ≤ (SS gates (13 + k.val)).card ∧ ∃ l : Fin 13, l ∉ B ∧
      ∀ u : Fin 13, val gates u (13 + k.val) = true → I u l := hH
  have hH2 : ∀ k ∈ H, 2 ≤ (SS gates (13 + k.val)).card ∧ ∃ l : Fin 13, l ∉ B ∧
      SS gates (13 + k.val) ⊆ Finset.univ.filter (fun p => I p l) := by
    intro k hk
    obtain ⟨h2, l, hlB, hsub⟩ := hH1 k hk
    refine ⟨h2, l, hlB, fun u hu => ?_⟩
    have hu' : u ∈ Finset.univ.filter (fun u => val gates u (13 + k.val) = true) := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub u (Finset.mem_filter.mp hu').2⟩
  exact count (fun k : Fin gates.length => SS gates (13 + k.val))
    (fun l => Finset.univ.filter (fun p => I p l)) hI4 hLu hLe (gate_cases gates hfan)
    B H hout2 hH2

end PEqualNP.Outside.L_meta_1619

theorem PEqualNP.Outside.L_meta_1619 : ∀ (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ l0 : Fin 13, (Finset.univ.filter (fun p0 : Fin 13 => I p0 l0)).card = 4) → (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (l2 u2 : Fin 13), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin 13 => decide (u2k = u2)))).getD (out l2) false = true ↔ I u2 l2) → ∀ (B : Finset (Fin 13)) (H : Finset (Fin gates.length)), (∀ k5 ∈ H, 2 ≤ (Finset.univ.filter (fun u5 : Fin 13 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin 13 => decide (u5k = u5)))).getD (13 + k5.val) false = true)).card ∧ ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u6 : Fin 13, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin 13 => decide (u6k = u6)))).getD (13 + k5.val) false = true → I u6 l4) → 3 * B.card + 2 * H.card ≤ 2 * gates.length :=
  PEqualNP.Outside.L_meta_1619.main_aux
