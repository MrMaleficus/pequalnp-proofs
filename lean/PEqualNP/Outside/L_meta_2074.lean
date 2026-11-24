import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2074
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

theorem main_aux : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → x2.support.ncard ≤ x4.size + (1 : ℕ) := by
  intro n G _ C h
  obtain ⟨⟨_, _, h2e⟩, hfun, _⟩ := h
  have h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => le_of_eq (h2e g hg)
  obtain ⟨T, hT, hTv⟩ := dep n C.gates h2 {C.output}
  have hall : ∀ v ∈ G.support, v.val ∈ T := by
    intro v hv
    obtain ⟨u, hvu⟩ := hv
    by_contra hk
    have hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
        (fun k : Fin n => decide (k = v ∨ k = u)) = true := by
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun
      exact Bool.or_eq_true_iff.mpr
        (Or.inr (decide_eq_true ⟨v, u, hvu, by simp, by simp⟩))
    have hy : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
        (fun k : Fin n => decide (k = u)) = false := by
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun
      refine Bool.or_eq_false_iff.mpr ⟨decide_eq_false ?_, decide_eq_false ?_⟩
      · rintro ⟨a, ha, _⟩
        simp at ha
      · rintro ⟨a, b, hab, ha, hb⟩
        have ha1 : a = u := of_decide_eq_true ha
        have hb1 : b = u := of_decide_eq_true hb
        exact hab.ne (ha1.trans hb1.symm)
    have hcx : PEqualNP.MetaComplexity.circuitFun n C
        (fun k : Fin n => decide (k = v ∨ k = u)) = true := by
      rw [hfun]; exact hx
    have hcy : PEqualNP.MetaComplexity.circuitFun n C
        (fun k : Fin n => decide (k = u)) = false := by
      rw [hfun]; exact hy
    have hag : ∀ k1 : Fin n, k1 ≠ v →
        (fun k : Fin n => decide (k = v ∨ k = u)) k1 = (fun k : Fin n => decide (k = u)) k1 := by
      intro k1 hk1
      show decide (k1 = v ∨ k1 = u) = decide (k1 = u)
      simp only [hk1, false_or]
    have he := hTv (List.ofFn (fun k : Fin n => decide (k = v ∨ k = u)))
      (List.ofFn (fun k : Fin n => decide (k = u))) (by simp) (by simp)
      (fun i hi => agree _ _ v hag i (fun h => hk (h ▸ hi))) C.output
      (Finset.mem_singleton_self _)
    have hx1 : (wf C.gates (List.ofFn (fun k : Fin n => decide (k = v ∨ k = u)))).getD
        C.output false = true := hcx
    have hy1 : (wf C.gates (List.ofFn (fun k : Fin n => decide (k = u)))).getD
        C.output false = false := hcy
    rw [hx1, hy1] at he
    exact Bool.noConfusion he
  have hle : G.support.ncard ≤ (↑T : Set ℕ).ncard :=
    Set.ncard_le_ncard_of_injOn (fun k : Fin n => k.val) hall
      (fun a _ b _ h => Fin.ext h) T.finite_toSet
  rw [Set.ncard_coe_finset] at hle
  rw [Finset.card_singleton] at hT
  show G.support.ncard ≤ C.gates.length + 1
  omega

end PEqualNP.Outside.L_meta_2074

theorem PEqualNP.Outside.L_meta_2074 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → x2.support.ncard ≤ x4.size + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_2074.main_aux
