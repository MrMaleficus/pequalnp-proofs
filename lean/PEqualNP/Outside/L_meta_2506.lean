import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2506
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem dep (n : ℕ) (pre : List Gate) : (∀ g ∈ pre, g.inputs.length ≤ 2) → ∀ S : Finset ℕ,
    ∃ T : Finset ℕ, T.card ≤ pre.length + S.card ∧ ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ w ∈ S, (wf pre x).getD w false = (wf pre y).getD w false := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro _ S
    exact ⟨S, by simp, fun x y _ _ h w hw => h w hw⟩
  | append_singleton pre g ih =>
    intro h2 S
    have h2p : ∀ g1 ∈ pre, g1.inputs.length ≤ 2 := fun g1 hg1 => h2 g1 (by simp [hg1])
    have hg : g.inputs.length ≤ 2 := h2 g (by simp)
    have key : ∀ (T : Finset ℕ) (S1 : Finset ℕ), (∀ w ∈ S, w ≠ n + pre.length → w ∈ S1) →
        (n + pre.length ∈ S → ∀ i ∈ g.inputs, i ∈ S1) →
        (∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S1, (wf pre x).getD w false = (wf pre y).getD w false) →
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S, (wf (pre ++ [g]) x).getD w false = (wf (pre ++ [g]) y).getD w false := by
      intro T S1 hS1 hin hI x y hx hy hag w hw
      have hI2 := hI x y hx hy hag
      rw [wf_snoc, wf_snoc]
      have hlx : (wf pre x).length = n + pre.length := by rw [wf_len, hx]
      have hly : (wf pre y).length = n + pre.length := by rw [wf_len, hy]
      rcases lt_trichotomy w (n + pre.length) with hlt | heq | hgt
      · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact hI2 w (hS1 w hw (by omega))
      · subst heq
        have e1 := getD_snoc_eq (wf pre x)
          (g.op.eval (g.inputs.map fun i => (wf pre x).getD i false))
        have e2 := getD_snoc_eq (wf pre y)
          (g.op.eval (g.inputs.map fun i => (wf pre y).getD i false))
        rw [hlx] at e1
        rw [hly] at e2
        rw [e1, e2]
        have hmap : (g.inputs.map fun i => (wf pre x).getD i false)
            = (g.inputs.map fun i => (wf pre y).getD i false) :=
          List.map_congr_left (fun i hi => hI2 i (hin hw i hi))
        rw [hmap]
      · rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]
    by_cases hm : (n + pre.length) ∈ S
    · obtain ⟨T, hT, hTv⟩ := ih h2p (S.erase (n + pre.length) ∪ g.inputs.toFinset)
      refine ⟨T, ?_, key T _ ?_ ?_ hTv⟩
      · have h1 := Finset.card_union_le (S.erase (n + pre.length)) g.inputs.toFinset
        have h3 := List.toFinset_card_le g.inputs
        have h4 := Finset.card_erase_of_mem hm
        have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hm⟩
        rw [List.length_append, List.length_singleton]
        omega
      · intro w hw hne
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
      · intro _ i hi
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)
    · obtain ⟨T, hT, hTv⟩ := ih h2p S
      refine ⟨T, ?_, key T S (fun w hw _ => hw) (fun h => absurd h hm) hTv⟩
      rw [List.length_append, List.length_singleton]
      omega

theorem ofFn_getD {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem agree {m : ℕ} (x y : Fin m → Bool) (k : Fin m)
    (h : ∀ k1 : Fin m, k1 ≠ k → x k1 = y k1) (i : ℕ) (hi : i ≠ k.val) :
    (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  by_cases hlt : i < m
  · rw [ofFn_getD x i hlt, ofFn_getD y i hlt]
    exact h ⟨i, hlt⟩ (fun he => hi (congrArg Fin.val he))
  · rw [List.getD_eq_default _ _ (by simpa using hlt),
      List.getD_eq_default _ _ (by simpa using hlt)]

theorem nat_ne_cast {N : ℕ} (a b : Fin N) : Fin.natAdd N a ≠ Fin.castAdd N b := by
  intro h
  have h1 : N + a.val = b.val := congrArg Fin.val h
  have h2 := b.isLt
  omega

theorem nat_inj {N : ℕ} (a b : Fin N) (h : Fin.natAdd N a = Fin.natAdd N b) : a = b := by
  have h1 : N + a.val = N + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

theorem card_le {N q : ℕ} (hq : 2 ≤ q) (l : Fin N) (z : Fin (N + N) → Bool)
    (hz : ∀ l1 : Fin N, z (Fin.natAdd N l1) = true → l1 = l) :
    (Finset.univ.filter (fun l1b : Fin N => z (Fin.natAdd N l1b) = true)).card ≤ q := by
  have hsub : (Finset.univ.filter (fun l1b : Fin N => z (Fin.natAdd N l1b) = true)) ⊆ {l} := by
    intro l1 h1
    exact Finset.mem_singleton.mpr (hz l1 (Finset.mem_filter.mp h1).2)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_singleton] at h1
  omega

theorem count : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1 := by
  intro q N I _ C hq hN hline huniq h2 hacc hrej
  have hN2 : 2 ≤ N := by omega
  have hsep : ∀ k : Fin (N + N), ∃ x y : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C x = true ∧
      PEqualNP.MetaComplexity.circuitFun (N + N) C y = false ∧
      ∀ k1 : Fin (N + N), k1 ≠ k → x k1 = y k1 := by
    intro k
    induction k using Fin.addCases with
    | left p =>
      obtain ⟨p2, hp2⟩ : ∃ p2 : Fin N, p ≠ p2 := by
        by_cases h0 : p.val = 0
        · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
          have h1 : p.val = 1 := congrArg Fin.val h
          omega
        · refine ⟨⟨0, by omega⟩, fun h => ?_⟩
          have h1 : p.val = 0 := congrArg Fin.val h
          exact h0 h1
      obtain ⟨l, hl, _⟩ := huniq p p2 hp2
      refine ⟨_, _, hacc p l hl.1,
        hrej (fun k1 => decide (k1 = Fin.natAdd N l))
          (card_le hq l (fun k1 => decide (k1 = Fin.natAdd N l)) ?_) ?_, ?_⟩
      · intro l1 h1
        exact nat_inj l1 l (of_decide_eq_true h1)
      · rintro ⟨p1, l1, _, h1, _⟩
        exact nat_ne_cast l p1 (of_decide_eq_true h1).symm
      · intro k1 hk1
        show decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l) = decide (k1 = Fin.natAdd N l)
        simp [hk1]
    | right l =>
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (lt_of_lt_of_eq (Nat.succ_pos q) (hline l).symm)
      have hpl : I p l := (Finset.mem_filter.mp hp).2
      refine ⟨_, _, hacc p l hpl,
        hrej (fun k1 => decide (k1 = Fin.castAdd N p))
          (card_le hq l (fun k1 => decide (k1 = Fin.castAdd N p)) ?_) ?_, ?_⟩
      · intro l1 h1
        exact absurd (of_decide_eq_true h1) (nat_ne_cast l1 p)
      · rintro ⟨p1, l1, _, _, h1⟩
        exact nat_ne_cast l1 p (of_decide_eq_true h1)
      · intro k1 hk1
        show decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l) = decide (k1 = Fin.castAdd N p)
        simp only [hk1, or_false]
  obtain ⟨T, hT, hTv⟩ := dep (N + N) C.gates h2 {C.output}
  have hall : ∀ k : Fin (N + N), k.val ∈ T := by
    intro k
    by_contra hk
    obtain ⟨x, y, hx, hy, hxy⟩ := hsep k
    have he := hTv (List.ofFn x) (List.ofFn y) (by simp) (by simp)
      (fun i hi => agree x y k hxy i (fun h => hk (h ▸ hi))) C.output
      (Finset.mem_singleton_self _)
    have hx1 : (wf C.gates (List.ofFn x)).getD C.output false = true := hx
    have hy1 : (wf C.gates (List.ofFn y)).getD C.output false = false := hy
    rw [hx1, hy1] at he
    exact Bool.noConfusion he
  have hcard : (Finset.univ : Finset (Fin (N + N))).card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun k => k.val) (fun k _ => hall k)
      (fun a _ b _ h => Fin.ext h)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  rw [Finset.card_singleton] at hT
  show 2 * N ≤ C.gates.length + 1
  omega

theorem main_aux : (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size) → ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * (q + 1) ≤ 112 * C.size := by
  intro H q N I _ C hq hN hline huniq hao hfun hread
  have hH : N * q ≤ 100 * C.size := H q N I C hq hN hline huniq hao hfun hread
  obtain ⟨_, _, hlen⟩ := hao
  have hs : 2 * N ≤ C.size + 1 :=
    count q N I C hq hN hline huniq (fun g hg => le_of_eq (hlen g hg))
      (fun p1 l1 h => by
        rw [hfun]
        exact decide_eq_true ⟨p1, l1, h, by simp, by simp⟩)
      (fun z1 _ hne => by
        rw [hfun]
        exact decide_eq_false hne)
  have e : N * (q + 1) = N * q + N := Nat.mul_succ N q
  have hN1 : 1 ≤ N := by omega
  rw [e]
  omega

end PEqualNP.Outside.L_meta_2506

theorem PEqualNP.Outside.L_meta_2506 : (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size) → ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * (q + 1) ≤ 112 * C.size :=
  PEqualNP.Outside.L_meta_2506.main_aux
