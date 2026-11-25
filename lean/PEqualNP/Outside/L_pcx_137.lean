import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_137

open PEqualNP.ProofComplexity

abbrev VV : Type := Fin 5 × Fin 2

def par (a : VV → Bool) (f : Finset VV) : Prop := Odd (f.filter (fun v => a v = true)).card

theorem card_sd (s t : Finset VV) : (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = (symmDiff s t) ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1; omega

theorem par_sd (a : VV → Bool) (s t : Finset VV) : par a (symmDiff s t) ↔ ¬ (par a s ↔ par a t) := by
  unfold par
  have hf : (symmDiff s t).filter (fun v => a v = true) =
      symmDiff (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  have := card_sd (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true))
  simp only [Nat.odd_iff]; omega

def sdl : List (LinEq VV) → Finset VV
  | [] => ∅
  | e :: l => symmDiff e.1 (sdl l)

def xbl : List (LinEq VV) → Bool
  | [] => false
  | e :: l => xor (!e.2) (xbl l)

theorem par_sdl (a : VV → Bool) (L : List (LinEq VV)) (h : ∀ e ∈ L, ¬ LinEqSat a e) :
    (par a (sdl L) ↔ xbl L = true) := by
  induction L with
  | nil => simp [par, sdl, xbl]
  | cons e l ih =>
    obtain ⟨f, b⟩ := e
    have he := h (f, b) (List.mem_cons_self ..)
    have hl := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he2 : par a f ↔ ¬ (b = true) := by
      unfold LinEqSat at he; unfold par; simp only at he; tauto
    simp only [sdl, xbl]
    rw [par_sd, hl, he2]
    cases b <;> cases xbl l <;> simp

def okB (q : LinEq VV) (D : LinClause VV) (L : List (LinEq VV)) : Bool :=
  L.all (fun e => decide (e ∈ D)) && decide (q.1 = sdl L) && (q.2 == !(xbl L))

theorem weak_cert (C D : LinClause VV) (certs : List (List (LinEq VV)))
    (h : ∀ q ∈ C, ∃ L ∈ certs, okB q D L = true) :
    ∀ a : VV → Bool, LinClauseSat a C → LinClauseSat a D := by
  intro a ⟨q, hq, hs⟩
  obtain ⟨L, _, hok⟩ := h q hq
  simp only [okB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hD, h1⟩, h2⟩ := hok
  by_contra hn
  have hn' : ∀ e ∈ L, ¬ LinEqSat a e := fun e he hse => hn ⟨e, hD e he, hse⟩
  have hp := par_sdl a L hn'
  unfold LinEqSat at hs
  rw [h1] at hs
  change par a (sdl L) ↔ q.2 = true at hs
  rw [hp, h2] at hs
  cases xbl L <;> simp at hs


def l0 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(0, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l1 : LinClause VV := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l2 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(0, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l3 : LinClause VV := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l4 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(1, 1)} : Finset VV), true), (({(1, 0)} : Finset VV), false), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l5 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l6 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(1, 1)} : Finset VV), false), (({(1, 0)} : Finset VV), false), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l7 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l8 : LinClause VV := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l9 : LinClause VV := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l10 : LinClause VV := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true)} : LinClause VV)

def l11 : LinClause VV := ({(({(0, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l12 : LinClause VV := ({(({(0, 0)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true), (({(0, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l13 : LinClause VV := ({(({(0, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(0, 1)} : Finset VV), false), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l14 : LinClause VV := ({(({(0, 0)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l15 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(2, 0)} : Finset VV), false), (({(2, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l16 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true), (({(0, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l17 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(2, 1)} : Finset VV), false), (({(0, 1)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l18 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l19 : LinClause VV := ({(({(0, 1), (2, 1)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l20 : LinClause VV := ({(({(0, 1), (2, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), true)} : LinClause VV)

def l21 : LinClause VV := ({(({(0, 1), (2, 1)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), true)} : LinClause VV)

def l22 : LinClause VV := ({(({(0, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l23 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l24 : LinClause VV := ({(({(3, 1)} : Finset VV), false), (({(0, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l25 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l26 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), false), (({(0, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l27 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 1), (3, 1)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l28 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(3, 1)} : Finset VV), false), (({(3, 0)} : Finset VV), false), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l29 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 1), (3, 1)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l30 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l31 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), true)} : LinClause VV)

def l32 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true)} : LinClause VV)

def l33 : LinClause VV := ({(({(0, 0)} : Finset VV), true), (({(4, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true), (({(4, 0)} : Finset VV), true)} : LinClause VV)

def l34 : LinClause VV := ({(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 0), (4, 0)} : Finset VV), true), (({(0, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l35 : LinClause VV := ({(({(0, 0)} : Finset VV), true), (({(4, 1)} : Finset VV), false), (({(0, 1)} : Finset VV), false), (({(4, 0)} : Finset VV), true)} : LinClause VV)

def l36 : LinClause VV := ({(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 0), (4, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false), (({(0, 0)} : Finset VV), true)} : LinClause VV)

def l37 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(4, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true), (({(4, 0)} : Finset VV), false)} : LinClause VV)

def l38 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 1), (4, 1)} : Finset VV), true), (({(0, 0), (4, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l39 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(4, 1)} : Finset VV), false), (({(0, 1)} : Finset VV), false), (({(4, 0)} : Finset VV), false)} : LinClause VV)

def l40 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 1), (4, 1)} : Finset VV), true), (({(0, 0), (4, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l41 : LinClause VV := ({(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 0), (4, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l42 : LinClause VV := ({(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), false), (({(0, 0), (4, 0)} : Finset VV), true)} : LinClause VV)

def l43 : LinClause VV := ({(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 0), (4, 0)} : Finset VV), true)} : LinClause VV)

def l44 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l45 : LinClause VV := ({(({(1, 0), (2, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l46 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(1, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l47 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(1, 0), (2, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(1, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l48 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l49 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 0), (2, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l50 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 1)} : Finset VV), false), (({(2, 1)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l51 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 0), (2, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), false), (({(1, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l52 : LinClause VV := ({(({(1, 0), (2, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l53 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(1, 0), (2, 0)} : Finset VV), true), (({(1, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l54 : LinClause VV := ({(({(1, 0), (2, 0)} : Finset VV), true), (({(1, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l55 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l56 : LinClause VV := ({(({(1, 0), (3, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 1), (3, 1)} : Finset VV), true)} : LinClause VV)

def l57 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(1, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), false)} : LinClause VV)

def l58 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(1, 0), (3, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(1, 1), (3, 1)} : Finset VV), true)} : LinClause VV)

def l59 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l60 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 0), (3, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 1), (3, 1)} : Finset VV), true)} : LinClause VV)

def l61 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 1)} : Finset VV), false), (({(3, 0)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : LinClause VV)

def l62 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 0), (3, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), false), (({(1, 1), (3, 1)} : Finset VV), true)} : LinClause VV)

def l63 : LinClause VV := ({(({(1, 0), (3, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 1), (3, 1)} : Finset VV), true)} : LinClause VV)

def l64 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(1, 0), (3, 0)} : Finset VV), true), (({(1, 1), (3, 1)} : Finset VV), true)} : LinClause VV)

def l65 : LinClause VV := ({(({(1, 0), (3, 0)} : Finset VV), true), (({(1, 1), (3, 1)} : Finset VV), true)} : LinClause VV)

def l66 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(4, 1)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(4, 0)} : Finset VV), true)} : LinClause VV)

def l67 : LinClause VV := ({(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l68 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(1, 0)} : Finset VV), true), (({(4, 1)} : Finset VV), false), (({(4, 0)} : Finset VV), true)} : LinClause VV)

def l69 : LinClause VV := ({(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), false), (({(1, 0)} : Finset VV), true), (({(1, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l70 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 1)} : Finset VV), true), (({(4, 1)} : Finset VV), true), (({(4, 0)} : Finset VV), false)} : LinClause VV)

def l71 : LinClause VV := ({(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 0)} : Finset VV), false), (({(1, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l72 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(1, 1)} : Finset VV), false), (({(4, 1)} : Finset VV), false), (({(4, 0)} : Finset VV), false)} : LinClause VV)

def l73 : LinClause VV := ({(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), false), (({(1, 0)} : Finset VV), false), (({(1, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l74 : LinClause VV := ({(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l75 : LinClause VV := ({(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), false), (({(1, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l76 : LinClause VV := ({(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l77 : LinClause VV := ({(({(3, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l78 : LinClause VV := ({(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 0), (3, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l79 : LinClause VV := ({(({(3, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l80 : LinClause VV := ({(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l81 : LinClause VV := ({(({(3, 0)} : Finset VV), false), (({(2, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l82 : LinClause VV := ({(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true)} : LinClause VV)

def l83 : LinClause VV := ({(({(3, 0)} : Finset VV), false), (({(2, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l84 : LinClause VV := ({(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l85 : LinClause VV := ({(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 0), (3, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true)} : LinClause VV)

def l86 : LinClause VV := ({(({(2, 1)} : Finset VV), false), (({(2, 1), (3, 1)} : Finset VV), true), (({(2, 0), (3, 0)} : Finset VV), true)} : LinClause VV)

def l87 : LinClause VV := ({(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 0), (3, 0)} : Finset VV), true)} : LinClause VV)

def l88 : LinClause VV := ({(({(4, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(4, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l89 : LinClause VV := ({(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 0), (4, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l90 : LinClause VV := ({(({(4, 1)} : Finset VV), false), (({(2, 1)} : Finset VV), false), (({(4, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l91 : LinClause VV := ({(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 0), (4, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l92 : LinClause VV := ({(({(4, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), false), (({(4, 0)} : Finset VV), false)} : LinClause VV)

def l93 : LinClause VV := ({(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 0), (4, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l94 : LinClause VV := ({(({(4, 1)} : Finset VV), false), (({(2, 1)} : Finset VV), false), (({(2, 0)} : Finset VV), false), (({(4, 0)} : Finset VV), false)} : LinClause VV)

def l95 : LinClause VV := ({(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 0), (4, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l96 : LinClause VV := ({(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 0), (4, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true)} : LinClause VV)

def l97 : LinClause VV := ({(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(2, 0), (4, 0)} : Finset VV), true)} : LinClause VV)

def l98 : LinClause VV := ({(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 0), (4, 0)} : Finset VV), true)} : LinClause VV)

def l99 : LinClause VV := ({(({(4, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(4, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l100 : LinClause VV := ({(({(3, 1)} : Finset VV), true), (({(3, 1), (4, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(3, 0), (4, 0)} : Finset VV), true)} : LinClause VV)

def l101 : LinClause VV := ({(({(4, 1)} : Finset VV), false), (({(3, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), false), (({(4, 0)} : Finset VV), true)} : LinClause VV)

def l102 : LinClause VV := ({(({(3, 1), (4, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), false), (({(3, 0), (4, 0)} : Finset VV), true)} : LinClause VV)

def l103 : LinClause VV := ({(({(3, 0)} : Finset VV), false), (({(4, 1)} : Finset VV), true), (({(4, 0)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l104 : LinClause VV := ({(({(3, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), false), (({(3, 1), (4, 1)} : Finset VV), true), (({(3, 0), (4, 0)} : Finset VV), true)} : LinClause VV)

def l105 : LinClause VV := ({(({(3, 0)} : Finset VV), false), (({(4, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false), (({(4, 0)} : Finset VV), false)} : LinClause VV)

def l106 : LinClause VV := ({(({(3, 0)} : Finset VV), false), (({(3, 1), (4, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), false), (({(3, 0), (4, 0)} : Finset VV), true)} : LinClause VV)

def l107 : LinClause VV := ({(({(3, 1)} : Finset VV), true), (({(3, 0), (4, 0)} : Finset VV), true), (({(3, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l108 : LinClause VV := ({(({(3, 1)} : Finset VV), false), (({(3, 0), (4, 0)} : Finset VV), true), (({(3, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l109 : LinClause VV := ({(({(3, 1), (4, 1)} : Finset VV), true), (({(3, 0), (4, 0)} : Finset VV), true)} : LinClause VV)

def l110 : LinClause VV := ({(({(2, 1), (3, 1)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)} : LinClause VV)

def l111 : LinClause VV := ({(({(0, 0), (4, 0)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), false), (({(2, 1), (4, 1)} : Finset VV), true)} : LinClause VV)

def l112 : LinClause VV := ({(({(0, 0), (4, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false), (({(2, 1), (3, 1)} : Finset VV), false), (({(2, 1), (4, 1)} : Finset VV), false)} : LinClause VV)

def l113 : LinClause VV := ({(({(0, 0), (4, 0)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), false), (({(2, 1), (3, 1)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)} : LinClause VV)

def l114 : LinClause VV := ({(({(0, 0), (4, 0)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)} : LinClause VV)

def l115 : LinClause VV := ({(({(0, 0), (4, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false), (({(0, 1), (4, 1)} : Finset VV), false)} : LinClause VV)

def l116 : LinClause VV := ({(({(0, 0), (4, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l117 : LinClause VV := ({(({(0, 0), (2, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l118 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l119 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l120 : LinClause VV := ({(({(0, 0), (2, 0)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l121 : LinClause VV := ({(({(0, 1), (2, 1)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l122 : LinClause VV := ({(({(0, 0), (2, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l123 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l124 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), true)} : LinClause VV)

def l125 : LinClause VV := ({(({(0, 1), (2, 1)} : Finset VV), false), (({(2, 0), (4, 0)} : Finset VV), true), (({(0, 1), (4, 1)} : Finset VV), false)} : LinClause VV)

def l126 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), false), (({(2, 0), (4, 0)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), false), (({(0, 1), (4, 1)} : Finset VV), false)} : LinClause VV)

def l127 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), false), (({(0, 1), (4, 1)} : Finset VV), false)} : LinClause VV)

def l128 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), false), (({(0, 1), (4, 1)} : Finset VV), false)} : LinClause VV)

def l129 : LinClause VV := ({(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (4, 0)} : Finset VV), false)} : LinClause VV)

def l130 : LinClause VV := ({(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), true)} : LinClause VV)

def l131 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), true), (({(0, 1), (2, 1)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), false)} : LinClause VV)

def l132 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), true)} : LinClause VV)

def l133 : LinClause VV := ({(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), true)} : LinClause VV)

def l134 : LinClause VV := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), false)} : LinClause VV)

def l135 : LinClause VV := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), false)} : LinClause VV)

def l136 : LinClause VV := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), true)} : LinClause VV)

def l137 : LinClause VV := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), false)} : LinClause VV)

def l138 : LinClause VV := ({(({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), true), (({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), false)} : LinClause VV)

def l139 : LinClause VV := ({(({(2, 0), (4, 0)} : Finset VV), true), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), false), (({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), false)} : LinClause VV)

def l140 : LinClause VV := ({(({(2, 0), (4, 0)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), false), (({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), false), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), false)} : LinClause VV)

def l141 : LinClause VV := ({(({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), false), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), false), (({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), false)} : LinClause VV)

def l142 : LinClause VV := ({(({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), false), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), false), (({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), false)} : LinClause VV)

def l143 : LinClause VV := ({(({(0, 0), (4, 0)} : Finset VV), true), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), true)} : LinClause VV)

def l144 : LinClause VV := ({(({(0, 0), (4, 0)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l145 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l146 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), false), (({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l147 : LinClause VV := ({(({(0, 0), (3, 0)} : Finset VV), true), (({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), true)} : LinClause VV)

def l148 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false), (({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l149 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l150 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l151 : LinClause VV := ({(({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), true)} : LinClause VV)

def l152 : LinClause VV := ({(({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l153 : LinClause VV := ({(({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l154 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), false)} : LinClause VV)

def l155 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), false)} : LinClause VV)

def l156 : LinClause VV := ({(({(0, 0), (1, 0)} : Finset VV), true)} : LinClause VV)

def l157 : LinClause VV := (∅ : LinClause VV)

def p0 : List (LinClause VV) := [l0]

def p1 : List (LinClause VV) := l1 :: p0

def p2 : List (LinClause VV) := l2 :: p1

def p3 : List (LinClause VV) := l3 :: p2

def p4 : List (LinClause VV) := l4 :: p3

def p5 : List (LinClause VV) := l5 :: p4

def p6 : List (LinClause VV) := l6 :: p5

def p7 : List (LinClause VV) := l7 :: p6

def p8 : List (LinClause VV) := l8 :: p7

def p9 : List (LinClause VV) := l9 :: p8

def p10 : List (LinClause VV) := l10 :: p9

def p11 : List (LinClause VV) := l11 :: p10

def p12 : List (LinClause VV) := l12 :: p11

def p13 : List (LinClause VV) := l13 :: p12

def p14 : List (LinClause VV) := l14 :: p13

def p15 : List (LinClause VV) := l15 :: p14

def p16 : List (LinClause VV) := l16 :: p15

def p17 : List (LinClause VV) := l17 :: p16

def p18 : List (LinClause VV) := l18 :: p17

def p19 : List (LinClause VV) := l19 :: p18

def p20 : List (LinClause VV) := l20 :: p19

def p21 : List (LinClause VV) := l21 :: p20

def p22 : List (LinClause VV) := l22 :: p21

def p23 : List (LinClause VV) := l23 :: p22

def p24 : List (LinClause VV) := l24 :: p23

def p25 : List (LinClause VV) := l25 :: p24

def p26 : List (LinClause VV) := l26 :: p25

def p27 : List (LinClause VV) := l27 :: p26

def p28 : List (LinClause VV) := l28 :: p27

def p29 : List (LinClause VV) := l29 :: p28

def p30 : List (LinClause VV) := l30 :: p29

def p31 : List (LinClause VV) := l31 :: p30

def p32 : List (LinClause VV) := l32 :: p31

def p33 : List (LinClause VV) := l33 :: p32

def p34 : List (LinClause VV) := l34 :: p33

def p35 : List (LinClause VV) := l35 :: p34

def p36 : List (LinClause VV) := l36 :: p35

def p37 : List (LinClause VV) := l37 :: p36

def p38 : List (LinClause VV) := l38 :: p37

def p39 : List (LinClause VV) := l39 :: p38

def p40 : List (LinClause VV) := l40 :: p39

def p41 : List (LinClause VV) := l41 :: p40

def p42 : List (LinClause VV) := l42 :: p41

def p43 : List (LinClause VV) := l43 :: p42

def p44 : List (LinClause VV) := l44 :: p43

def p45 : List (LinClause VV) := l45 :: p44

def p46 : List (LinClause VV) := l46 :: p45

def p47 : List (LinClause VV) := l47 :: p46

def p48 : List (LinClause VV) := l48 :: p47

def p49 : List (LinClause VV) := l49 :: p48

def p50 : List (LinClause VV) := l50 :: p49

def p51 : List (LinClause VV) := l51 :: p50

def p52 : List (LinClause VV) := l52 :: p51

def p53 : List (LinClause VV) := l53 :: p52

def p54 : List (LinClause VV) := l54 :: p53

def p55 : List (LinClause VV) := l55 :: p54

def p56 : List (LinClause VV) := l56 :: p55

def p57 : List (LinClause VV) := l57 :: p56

def p58 : List (LinClause VV) := l58 :: p57

def p59 : List (LinClause VV) := l59 :: p58

def p60 : List (LinClause VV) := l60 :: p59

def p61 : List (LinClause VV) := l61 :: p60

def p62 : List (LinClause VV) := l62 :: p61

def p63 : List (LinClause VV) := l63 :: p62

def p64 : List (LinClause VV) := l64 :: p63

def p65 : List (LinClause VV) := l65 :: p64

def p66 : List (LinClause VV) := l66 :: p65

def p67 : List (LinClause VV) := l67 :: p66

def p68 : List (LinClause VV) := l68 :: p67

def p69 : List (LinClause VV) := l69 :: p68

def p70 : List (LinClause VV) := l70 :: p69

def p71 : List (LinClause VV) := l71 :: p70

def p72 : List (LinClause VV) := l72 :: p71

def p73 : List (LinClause VV) := l73 :: p72

def p74 : List (LinClause VV) := l74 :: p73

def p75 : List (LinClause VV) := l75 :: p74

def p76 : List (LinClause VV) := l76 :: p75

def p77 : List (LinClause VV) := l77 :: p76

def p78 : List (LinClause VV) := l78 :: p77

def p79 : List (LinClause VV) := l79 :: p78

def p80 : List (LinClause VV) := l80 :: p79

def p81 : List (LinClause VV) := l81 :: p80

def p82 : List (LinClause VV) := l82 :: p81

def p83 : List (LinClause VV) := l83 :: p82

def p84 : List (LinClause VV) := l84 :: p83

def p85 : List (LinClause VV) := l85 :: p84

def p86 : List (LinClause VV) := l86 :: p85

def p87 : List (LinClause VV) := l87 :: p86

def p88 : List (LinClause VV) := l88 :: p87

def p89 : List (LinClause VV) := l89 :: p88

def p90 : List (LinClause VV) := l90 :: p89

def p91 : List (LinClause VV) := l91 :: p90

def p92 : List (LinClause VV) := l92 :: p91

def p93 : List (LinClause VV) := l93 :: p92

def p94 : List (LinClause VV) := l94 :: p93

def p95 : List (LinClause VV) := l95 :: p94

def p96 : List (LinClause VV) := l96 :: p95

def p97 : List (LinClause VV) := l97 :: p96

def p98 : List (LinClause VV) := l98 :: p97

def p99 : List (LinClause VV) := l99 :: p98

def p100 : List (LinClause VV) := l100 :: p99

def p101 : List (LinClause VV) := l101 :: p100

def p102 : List (LinClause VV) := l102 :: p101

def p103 : List (LinClause VV) := l103 :: p102

def p104 : List (LinClause VV) := l104 :: p103

def p105 : List (LinClause VV) := l105 :: p104

def p106 : List (LinClause VV) := l106 :: p105

def p107 : List (LinClause VV) := l107 :: p106

def p108 : List (LinClause VV) := l108 :: p107

def p109 : List (LinClause VV) := l109 :: p108

def p110 : List (LinClause VV) := l110 :: p109

def p111 : List (LinClause VV) := l111 :: p110

def p112 : List (LinClause VV) := l112 :: p111

def p113 : List (LinClause VV) := l113 :: p112

def p114 : List (LinClause VV) := l114 :: p113

def p115 : List (LinClause VV) := l115 :: p114

def p116 : List (LinClause VV) := l116 :: p115

def p117 : List (LinClause VV) := l117 :: p116

def p118 : List (LinClause VV) := l118 :: p117

def p119 : List (LinClause VV) := l119 :: p118

def p120 : List (LinClause VV) := l120 :: p119

def p121 : List (LinClause VV) := l121 :: p120

def p122 : List (LinClause VV) := l122 :: p121

def p123 : List (LinClause VV) := l123 :: p122

def p124 : List (LinClause VV) := l124 :: p123

def p125 : List (LinClause VV) := l125 :: p124

def p126 : List (LinClause VV) := l126 :: p125

def p127 : List (LinClause VV) := l127 :: p126

def p128 : List (LinClause VV) := l128 :: p127

def p129 : List (LinClause VV) := l129 :: p128

def p130 : List (LinClause VV) := l130 :: p129

def p131 : List (LinClause VV) := l131 :: p130

def p132 : List (LinClause VV) := l132 :: p131

def p133 : List (LinClause VV) := l133 :: p132

def p134 : List (LinClause VV) := l134 :: p133

def p135 : List (LinClause VV) := l135 :: p134

def p136 : List (LinClause VV) := l136 :: p135

def p137 : List (LinClause VV) := l137 :: p136

def p138 : List (LinClause VV) := l138 :: p137

def p139 : List (LinClause VV) := l139 :: p138

def p140 : List (LinClause VV) := l140 :: p139

def p141 : List (LinClause VV) := l141 :: p140

def p142 : List (LinClause VV) := l142 :: p141

def p143 : List (LinClause VV) := l143 :: p142

def p144 : List (LinClause VV) := l144 :: p143

def p145 : List (LinClause VV) := l145 :: p144

def p146 : List (LinClause VV) := l146 :: p145

def p147 : List (LinClause VV) := l147 :: p146

def p148 : List (LinClause VV) := l148 :: p147

def p149 : List (LinClause VV) := l149 :: p148

def p150 : List (LinClause VV) := l150 :: p149

def p151 : List (LinClause VV) := l151 :: p150

def p152 : List (LinClause VV) := l152 :: p151

def p153 : List (LinClause VV) := l153 :: p152

def p154 : List (LinClause VV) := l154 :: p153

def p155 : List (LinClause VV) := l155 :: p154

def p156 : List (LinClause VV) := l156 :: p155

def p157 : List (LinClause VV) := l157 :: p156

set_option maxRecDepth 100000 in
theorem d0 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p0 :=
  IsLinDerivation.ax IsLinDerivation.nil ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨0, 1, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d1 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p1 :=
  IsLinDerivation.weak (C := l0) d0 (List.Mem.head _) (weak_cert l0 l1 [[(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true)], [(({(0, 0)} : Finset VV), true)], [(({(0, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d2 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p2 :=
  IsLinDerivation.ax d1 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨0, 1, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d3 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p3 :=
  IsLinDerivation.weak (C := l2) d2 (List.Mem.head _) (weak_cert l2 l3 [[(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), false)], [(({(0, 0)} : Finset VV), true)], [(({(0, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d4 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p4 :=
  IsLinDerivation.ax d3 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨0, 1, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d5 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p5 :=
  IsLinDerivation.weak (C := l4) d4 (List.Mem.head _) (weak_cert l4 l5 [[(({(0, 0)} : Finset VV), false)], [(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true)], [(({(0, 0)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d6 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p6 :=
  IsLinDerivation.ax d5 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨0, 1, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d7 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p7 :=
  IsLinDerivation.weak (C := l6) d6 (List.Mem.head _) (weak_cert l6 l7 [[(({(0, 0)} : Finset VV), false)], [(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), false)], [(({(0, 0)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d8 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p8 :=
  IsLinDerivation.res (C := l5) (D := l1) d7 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d9 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p9 :=
  IsLinDerivation.res (C := l7) (D := l3) d8 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d10 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p10 :=
  IsLinDerivation.res (C := l9) (D := l8) d9 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(0, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d11 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p11 :=
  IsLinDerivation.ax d10 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨0, 2, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d12 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p12 :=
  IsLinDerivation.weak (C := l11) d11 (List.Mem.head _) (weak_cert l11 l12 [[(({(0, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true), (({(0, 1), (2, 1)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true)], [(({(0, 0)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d13 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p13 :=
  IsLinDerivation.ax d12 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨0, 2, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d14 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p14 :=
  IsLinDerivation.weak (C := l13) d13 (List.Mem.head _) (weak_cert l13 l14 [[(({(0, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), true)], [(({(0, 1)} : Finset VV), false)], [(({(0, 0)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d15 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p15 :=
  IsLinDerivation.ax d14 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨0, 2, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d16 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p16 :=
  IsLinDerivation.weak (C := l15) d15 (List.Mem.head _) (weak_cert l15 l16 [[(({(0, 0)} : Finset VV), false)], [(({(0, 0)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true), (({(0, 1), (2, 1)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d17 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p17 :=
  IsLinDerivation.ax d16 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨0, 2, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d18 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p18 :=
  IsLinDerivation.weak (C := l17) d17 (List.Mem.head _) (weak_cert l17 l18 [[(({(0, 0)} : Finset VV), false)], [(({(0, 1)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), true)], [(({(0, 1)} : Finset VV), false)], [(({(0, 0)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d19 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p19 :=
  IsLinDerivation.res (C := l16) (D := l12) d18 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d20 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p20 :=
  IsLinDerivation.res (C := l18) (D := l14) d19 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d21 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p21 :=
  IsLinDerivation.res (C := l20) (D := l19) d20 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(0, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d22 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p22 :=
  IsLinDerivation.ax d21 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨0, 3, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d23 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p23 :=
  IsLinDerivation.weak (C := l22) d22 (List.Mem.head _) (weak_cert l22 l23 [[(({(0, 0)} : Finset VV), true)], [(({(0, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true)], [(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d24 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p24 :=
  IsLinDerivation.ax d23 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨0, 3, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d25 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p25 :=
  IsLinDerivation.weak (C := l24) d24 (List.Mem.head _) (weak_cert l24 l25 [[(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), false)], [(({(0, 0)} : Finset VV), true)], [(({(0, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d26 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p26 :=
  IsLinDerivation.ax d25 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨0, 3, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d27 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p27 :=
  IsLinDerivation.weak (C := l26) d26 (List.Mem.head _) (weak_cert l26 l27 [[(({(0, 0)} : Finset VV), false)], [(({(0, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true)], [(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d28 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p28 :=
  IsLinDerivation.ax d27 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨0, 3, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d29 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p29 :=
  IsLinDerivation.weak (C := l28) d28 (List.Mem.head _) (weak_cert l28 l29 [[(({(0, 0)} : Finset VV), false)], [(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), false)], [(({(0, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d30 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p30 :=
  IsLinDerivation.res (C := l27) (D := l23) d29 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d31 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p31 :=
  IsLinDerivation.res (C := l29) (D := l25) d30 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d32 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p32 :=
  IsLinDerivation.res (C := l31) (D := l30) d31 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(0, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d33 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p33 :=
  IsLinDerivation.ax d32 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨0, 4, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d34 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p34 :=
  IsLinDerivation.weak (C := l33) d33 (List.Mem.head _) (weak_cert l33 l34 [[(({(0, 0)} : Finset VV), true)], [(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true)], [(({(0, 0), (4, 0)} : Finset VV), true), (({(0, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d35 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p35 :=
  IsLinDerivation.ax d34 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨0, 4, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d36 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p36 :=
  IsLinDerivation.weak (C := l35) d35 (List.Mem.head _) (weak_cert l35 l36 [[(({(0, 0)} : Finset VV), true)], [(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), false)], [(({(0, 1)} : Finset VV), false)], [(({(0, 0), (4, 0)} : Finset VV), true), (({(0, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d37 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p37 :=
  IsLinDerivation.ax d36 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨0, 4, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d38 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p38 :=
  IsLinDerivation.weak (C := l37) d37 (List.Mem.head _) (weak_cert l37 l38 [[(({(0, 0)} : Finset VV), false)], [(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true)], [(({(0, 0)} : Finset VV), false), (({(0, 0), (4, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d39 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p39 :=
  IsLinDerivation.ax d38 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((0 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨0, 4, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d40 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p40 :=
  IsLinDerivation.weak (C := l39) d39 (List.Mem.head _) (weak_cert l39 l40 [[(({(0, 0)} : Finset VV), false)], [(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 1)} : Finset VV), false)], [(({(0, 1)} : Finset VV), false)], [(({(0, 0)} : Finset VV), false), (({(0, 0), (4, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d41 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p41 :=
  IsLinDerivation.res (C := l38) (D := l34) d40 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d42 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p42 :=
  IsLinDerivation.res (C := l40) (D := l36) d41 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d43 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p43 :=
  IsLinDerivation.res (C := l42) (D := l41) d42 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(0, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d44 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p44 :=
  IsLinDerivation.ax d43 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨1, 2, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d45 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p45 :=
  IsLinDerivation.weak (C := l44) d44 (List.Mem.head _) (weak_cert l44 l45 [[(({(1, 0)} : Finset VV), true)], [(({(1, 1)} : Finset VV), true), (({(1, 1), (2, 1)} : Finset VV), true)], [(({(1, 1)} : Finset VV), true)], [(({(1, 0), (2, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d46 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p46 :=
  IsLinDerivation.ax d45 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨1, 2, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d47 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p47 :=
  IsLinDerivation.weak (C := l46) d46 (List.Mem.head _) (weak_cert l46 l47 [[(({(1, 1)} : Finset VV), false)], [(({(1, 0)} : Finset VV), true)], [(({(1, 1)} : Finset VV), false), (({(1, 1), (2, 1)} : Finset VV), true)], [(({(1, 0), (2, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d48 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p48 :=
  IsLinDerivation.ax d47 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨1, 2, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d49 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p49 :=
  IsLinDerivation.weak (C := l48) d48 (List.Mem.head _) (weak_cert l48 l49 [[(({(1, 0)} : Finset VV), false)], [(({(1, 1)} : Finset VV), true)], [(({(1, 1)} : Finset VV), true), (({(1, 1), (2, 1)} : Finset VV), true)], [(({(1, 0)} : Finset VV), false), (({(1, 0), (2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d50 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p50 :=
  IsLinDerivation.ax d49 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨1, 2, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d51 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p51 :=
  IsLinDerivation.weak (C := l50) d50 (List.Mem.head _) (weak_cert l50 l51 [[(({(1, 0)} : Finset VV), false)], [(({(1, 1)} : Finset VV), false)], [(({(1, 1)} : Finset VV), false), (({(1, 1), (2, 1)} : Finset VV), true)], [(({(1, 0)} : Finset VV), false), (({(1, 0), (2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d52 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p52 :=
  IsLinDerivation.res (C := l49) (D := l45) d51 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d53 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p53 :=
  IsLinDerivation.res (C := l51) (D := l47) d52 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d54 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p54 :=
  IsLinDerivation.res (C := l53) (D := l52) d53 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d55 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p55 :=
  IsLinDerivation.ax d54 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨1, 3, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d56 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p56 :=
  IsLinDerivation.weak (C := l55) d55 (List.Mem.head _) (weak_cert l55 l56 [[(({(1, 0)} : Finset VV), true)], [(({(1, 0), (3, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true)], [(({(1, 1)} : Finset VV), true)], [(({(1, 1)} : Finset VV), true), (({(1, 1), (3, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d57 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p57 :=
  IsLinDerivation.ax d56 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨1, 3, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d58 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p58 :=
  IsLinDerivation.weak (C := l57) d57 (List.Mem.head _) (weak_cert l57 l58 [[(({(1, 1)} : Finset VV), false)], [(({(1, 0)} : Finset VV), true)], [(({(1, 0), (3, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true)], [(({(1, 1)} : Finset VV), false), (({(1, 1), (3, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d59 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p59 :=
  IsLinDerivation.ax d58 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨1, 3, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d60 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p60 :=
  IsLinDerivation.weak (C := l59) d59 (List.Mem.head _) (weak_cert l59 l60 [[(({(1, 0)} : Finset VV), false)], [(({(1, 1)} : Finset VV), true)], [(({(1, 0)} : Finset VV), false), (({(1, 0), (3, 0)} : Finset VV), true)], [(({(1, 1)} : Finset VV), true), (({(1, 1), (3, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d61 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p61 :=
  IsLinDerivation.ax d60 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨1, 3, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d62 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p62 :=
  IsLinDerivation.weak (C := l61) d61 (List.Mem.head _) (weak_cert l61 l62 [[(({(1, 0)} : Finset VV), false)], [(({(1, 1)} : Finset VV), false)], [(({(1, 0)} : Finset VV), false), (({(1, 0), (3, 0)} : Finset VV), true)], [(({(1, 1)} : Finset VV), false), (({(1, 1), (3, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d63 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p63 :=
  IsLinDerivation.res (C := l60) (D := l56) d62 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d64 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p64 :=
  IsLinDerivation.res (C := l62) (D := l58) d63 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d65 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p65 :=
  IsLinDerivation.res (C := l64) (D := l63) d64 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d66 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p66 :=
  IsLinDerivation.ax d65 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨1, 4, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d67 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p67 :=
  IsLinDerivation.weak (C := l66) d66 (List.Mem.head _) (weak_cert l66 l67 [[(({(1, 0)} : Finset VV), true)], [(({(1, 1)} : Finset VV), true), (({(1, 1), (4, 1)} : Finset VV), true)], [(({(1, 1)} : Finset VV), true)], [(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d68 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p68 :=
  IsLinDerivation.ax d67 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨1, 4, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d69 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p69 :=
  IsLinDerivation.weak (C := l68) d68 (List.Mem.head _) (weak_cert l68 l69 [[(({(1, 1)} : Finset VV), false)], [(({(1, 0)} : Finset VV), true)], [(({(1, 1)} : Finset VV), false), (({(1, 1), (4, 1)} : Finset VV), true)], [(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d70 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p70 :=
  IsLinDerivation.ax d69 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨1, 4, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d71 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p71 :=
  IsLinDerivation.weak (C := l70) d70 (List.Mem.head _) (weak_cert l70 l71 [[(({(1, 0)} : Finset VV), false)], [(({(1, 1)} : Finset VV), true)], [(({(1, 1)} : Finset VV), true), (({(1, 1), (4, 1)} : Finset VV), true)], [(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d72 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p72 :=
  IsLinDerivation.ax d71 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((1 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨1, 4, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d73 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p73 :=
  IsLinDerivation.weak (C := l72) d72 (List.Mem.head _) (weak_cert l72 l73 [[(({(1, 0)} : Finset VV), false)], [(({(1, 1)} : Finset VV), false)], [(({(1, 1)} : Finset VV), false), (({(1, 1), (4, 1)} : Finset VV), true)], [(({(1, 0), (4, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d74 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p74 :=
  IsLinDerivation.res (C := l71) (D := l67) d73 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d75 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p75 :=
  IsLinDerivation.res (C := l73) (D := l69) d74 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d76 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p76 :=
  IsLinDerivation.res (C := l75) (D := l74) d75 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d77 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p77 :=
  IsLinDerivation.ax d76 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨2, 3, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d78 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p78 :=
  IsLinDerivation.weak (C := l77) d77 (List.Mem.head _) (weak_cert l77 l78 [[(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true)], [(({(2, 0), (3, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true)], [(({(2, 1)} : Finset VV), true)], [(({(2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d79 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p79 :=
  IsLinDerivation.ax d78 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨2, 3, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d80 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p80 :=
  IsLinDerivation.weak (C := l79) d79 (List.Mem.head _) (weak_cert l79 l80 [[(({(2, 0), (3, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true)], [(({(2, 1)} : Finset VV), false)], [(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), false)], [(({(2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d81 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p81 :=
  IsLinDerivation.ax d80 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨2, 3, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d82 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p82 :=
  IsLinDerivation.weak (C := l81) d81 (List.Mem.head _) (weak_cert l81 l82 [[(({(2, 0)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), true)], [(({(2, 1)} : Finset VV), true)], [(({(2, 0)} : Finset VV), false)], [(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d83 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p83 :=
  IsLinDerivation.ax d82 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨2, 3, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d84 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p84 :=
  IsLinDerivation.weak (C := l83) d83 (List.Mem.head _) (weak_cert l83 l84 [[(({(2, 0), (3, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), false)], [(({(2, 1)} : Finset VV), false)], [(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), false)], [(({(2, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d85 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p85 :=
  IsLinDerivation.res (C := l82) (D := l78) d84 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d86 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p86 :=
  IsLinDerivation.res (C := l84) (D := l80) d85 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d87 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p87 :=
  IsLinDerivation.res (C := l86) (D := l85) d86 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d88 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p88 :=
  IsLinDerivation.ax d87 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨2, 4, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d89 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p89 :=
  IsLinDerivation.weak (C := l88) d88 (List.Mem.head _) (weak_cert l88 l89 [[(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true)], [(({(2, 1)} : Finset VV), true)], [(({(2, 0), (4, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true)], [(({(2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d90 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p90 :=
  IsLinDerivation.ax d89 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨2, 4, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d91 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p91 :=
  IsLinDerivation.weak (C := l90) d90 (List.Mem.head _) (weak_cert l90 l91 [[(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), false)], [(({(2, 1)} : Finset VV), false)], [(({(2, 0), (4, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true)], [(({(2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d92 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p92 :=
  IsLinDerivation.ax d91 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨2, 4, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d93 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p93 :=
  IsLinDerivation.weak (C := l92) d92 (List.Mem.head _) (weak_cert l92 l93 [[(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true)], [(({(2, 1)} : Finset VV), true)], [(({(2, 0)} : Finset VV), false)], [(({(2, 0), (4, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d94 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p94 :=
  IsLinDerivation.ax d93 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((2 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨2, 4, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d95 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p95 :=
  IsLinDerivation.weak (C := l94) d94 (List.Mem.head _) (weak_cert l94 l95 [[(({(2, 1), (4, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), false)], [(({(2, 1)} : Finset VV), false)], [(({(2, 0)} : Finset VV), false)], [(({(2, 0), (4, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d96 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p96 :=
  IsLinDerivation.res (C := l93) (D := l89) d95 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d97 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p97 :=
  IsLinDerivation.res (C := l95) (D := l91) d96 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d98 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p98 :=
  IsLinDerivation.res (C := l97) (D := l96) d97 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d99 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p99 :=
  IsLinDerivation.ax d98 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![false, false] : Fin 2 → Bool) b))), ⟨3, 4, ![false, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d100 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p100 :=
  IsLinDerivation.weak (C := l99) d99 (List.Mem.head _) (weak_cert l99 l100 [[(({(3, 1)} : Finset VV), true), (({(3, 1), (4, 1)} : Finset VV), true)], [(({(3, 0)} : Finset VV), true)], [(({(3, 0)} : Finset VV), true), (({(3, 0), (4, 0)} : Finset VV), true)], [(({(3, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d101 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p101 :=
  IsLinDerivation.ax d100 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![false, true] : Fin 2 → Bool) b))), ⟨3, 4, ![false, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d102 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p102 :=
  IsLinDerivation.weak (C := l101) d101 (List.Mem.head _) (weak_cert l101 l102 [[(({(3, 1), (4, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), false)], [(({(3, 0)} : Finset VV), true)], [(({(3, 1)} : Finset VV), false)], [(({(3, 0)} : Finset VV), true), (({(3, 0), (4, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d103 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p103 :=
  IsLinDerivation.ax d102 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![true, false] : Fin 2 → Bool) b))), ⟨3, 4, ![true, false], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d104 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p104 :=
  IsLinDerivation.weak (C := l103) d103 (List.Mem.head _) (weak_cert l103 l104 [[(({(3, 0)} : Finset VV), false)], [(({(3, 1)} : Finset VV), true), (({(3, 1), (4, 1)} : Finset VV), true)], [(({(3, 0)} : Finset VV), false), (({(3, 0), (4, 0)} : Finset VV), true)], [(({(3, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d105 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p105 :=
  IsLinDerivation.ax d104 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun b : Fin 2 => (((3 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b)) ∪ Finset.univ.image (fun b : Fin 2 => (((4 : Fin 5), b), !(![true, true] : Fin 2 → Bool) b))), ⟨3, 4, ![true, true], by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d106 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p106 :=
  IsLinDerivation.weak (C := l105) d105 (List.Mem.head _) (weak_cert l105 l106 [[(({(3, 0)} : Finset VV), false)], [(({(3, 1), (4, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), false)], [(({(3, 1)} : Finset VV), false)], [(({(3, 0)} : Finset VV), false), (({(3, 0), (4, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d107 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p107 :=
  IsLinDerivation.res (C := l104) (D := l100) d106 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d108 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p108 :=
  IsLinDerivation.res (C := l106) (D := l102) d107 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d109 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p109 :=
  IsLinDerivation.res (C := l108) (D := l107) d108 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d110 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p110 :=
  IsLinDerivation.weak (C := l87) d109 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))) (weak_cert l87 l110 [[(({(2, 1), (3, 1)} : Finset VV), true)], [(({(0, 0), (2, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d111 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p111 :=
  IsLinDerivation.weak (C := l98) d110 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))) (weak_cert l98 l111 [[(({(2, 1), (4, 1)} : Finset VV), true)], [(({(0, 0), (4, 0)} : Finset VV), false), (({(0, 0), (2, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d112 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p112 :=
  IsLinDerivation.weak (C := l109) d111 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (weak_cert l109 l112 [[(({(2, 1), (3, 1)} : Finset VV), false), (({(2, 1), (4, 1)} : Finset VV), false)], [(({(0, 0), (4, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d113 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p113 :=
  IsLinDerivation.res (C := l112) (D := l111) d112 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(2, 1), (4, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d114 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p114 :=
  IsLinDerivation.res (C := l113) (D := l110) d113 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) ⟨({(2, 1), (3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d115 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p115 :=
  IsLinDerivation.weak (C := l76) d114 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) (weak_cert l76 l115 [[(({(0, 0), (4, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true)], [(({(0, 1), (1, 1)} : Finset VV), false), (({(0, 1), (4, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d116 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p116 :=
  IsLinDerivation.res (C := l115) (D := l43) d115 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ⟨({(0, 1), (4, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d117 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p117 :=
  IsLinDerivation.res (C := l114) (D := l116) d116 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({(0, 0), (4, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d118 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p118 :=
  IsLinDerivation.weak (C := l65) d117 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l65 l118 [[(({(0, 0), (1, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true)], [(({(0, 1), (3, 1)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d119 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p119 :=
  IsLinDerivation.res (C := l118) (D := l32) d118 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ⟨({(0, 1), (3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d120 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p120 :=
  IsLinDerivation.res (C := l117) (D := l119) d119 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({(0, 0), (3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d121 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p121 :=
  IsLinDerivation.weak (C := l54) d120 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l54 l121 [[(({(0, 0), (2, 0)} : Finset VV), true), (({(0, 0), (1, 0)} : Finset VV), true)], [(({(0, 1), (2, 1)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d122 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p122 :=
  IsLinDerivation.res (C := l121) (D := l21) d121 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ⟨({(0, 1), (2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d123 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p123 :=
  IsLinDerivation.res (C := l120) (D := l122) d122 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({(0, 0), (2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d124 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p124 :=
  IsLinDerivation.weak (C := l87) d123 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))) (weak_cert l87 l124 [[(({(0, 1), (3, 1)} : Finset VV), false), (({(0, 1), (2, 1)} : Finset VV), false)], [(({(2, 0), (3, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d125 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p125 :=
  IsLinDerivation.weak (C := l98) d124 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))) (weak_cert l98 l125 [[(({(0, 1), (2, 1)} : Finset VV), false), (({(0, 1), (4, 1)} : Finset VV), false)], [(({(2, 0), (4, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d126 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p126 :=
  IsLinDerivation.weak (C := l109) d125 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) (weak_cert l109 l126 [[(({(0, 1), (3, 1)} : Finset VV), false), (({(0, 1), (4, 1)} : Finset VV), false)], [(({(2, 0), (4, 0)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d127 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p127 :=
  IsLinDerivation.res (C := l126) (D := l125) d126 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(2, 0), (4, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d128 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p128 :=
  IsLinDerivation.res (C := l127) (D := l124) d127 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) ⟨({(2, 0), (3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d129 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p129 :=
  IsLinDerivation.weak (C := l76) d128 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l76 l129 [[(({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (4, 0)} : Finset VV), false)], [(({(0, 1), (4, 1)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d130 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p130 :=
  IsLinDerivation.res (C := l129) (D := l43) d129 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ⟨({(0, 0), (4, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d131 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p131 :=
  IsLinDerivation.res (C := l128) (D := l130) d130 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({(0, 1), (4, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d132 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p132 :=
  IsLinDerivation.weak (C := l65) d131 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l65 l132 [[(({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)], [(({(0, 1), (3, 1)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d133 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p133 :=
  IsLinDerivation.res (C := l132) (D := l32) d132 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ⟨({(0, 0), (3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d134 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p134 :=
  IsLinDerivation.res (C := l131) (D := l133) d133 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({(0, 1), (3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d135 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p135 :=
  IsLinDerivation.weak (C := l54) d134 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l54 l135 [[(({(0, 0), (2, 0)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), false)], [(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 1), (2, 1)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d136 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p136 :=
  IsLinDerivation.res (C := l135) (D := l21) d135 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ⟨({(0, 0), (2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d137 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p137 :=
  IsLinDerivation.res (C := l134) (D := l136) d136 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({(0, 1), (2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d138 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p138 :=
  IsLinDerivation.weak (C := l87) d137 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l87 l138 [[(({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), true), (({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), false)], [(({(2, 0), (3, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d139 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p139 :=
  IsLinDerivation.weak (C := l98) d138 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))) (weak_cert l98 l139 [[(({(2, 0), (4, 0)} : Finset VV), true), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), false), (({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), false)], [(({(2, 0), (4, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d140 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p140 :=
  IsLinDerivation.weak (C := l109) d139 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))) (weak_cert l109 l140 [[(({(2, 0), (4, 0)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), false), (({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), false), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), false)], [(({(2, 0), (4, 0)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d141 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p141 :=
  IsLinDerivation.res (C := l140) (D := l139) d140 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(2, 0), (4, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d142 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p142 :=
  IsLinDerivation.res (C := l141) (D := l138) d141 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) ⟨({(2, 0), (3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d143 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p143 :=
  IsLinDerivation.weak (C := l43) d142 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l43 l143 [[(({(0, 0), (4, 0)} : Finset VV), true), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), true)], [(({(0, 0), (4, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d144 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p144 :=
  IsLinDerivation.weak (C := l76) d143 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l76 l144 [[(({(0, 0), (4, 0)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), false)], [(({(0, 0), (4, 0)} : Finset VV), false), (({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d145 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p145 :=
  IsLinDerivation.res (C := l144) (D := l143) d144 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(0, 0), (4, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d146 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p146 :=
  IsLinDerivation.res (C := l142) (D := l145) d145 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) ⟨({(0, 0), (0, 1), (4, 0), (4, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d147 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p147 :=
  IsLinDerivation.weak (C := l32) d146 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l32 l147 [[(({(0, 0), (3, 0)} : Finset VV), true), (({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), true)], [(({(0, 0), (3, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d148 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p148 :=
  IsLinDerivation.weak (C := l65) d147 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l65 l148 [[(({(0, 0), (1, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)], [(({(0, 0), (3, 0)} : Finset VV), false), (({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d149 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p149 :=
  IsLinDerivation.res (C := l148) (D := l147) d148 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(0, 0), (3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d150 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p150 :=
  IsLinDerivation.res (C := l146) (D := l149) d149 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) ⟨({(0, 0), (0, 1), (3, 0), (3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d151 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p151 :=
  IsLinDerivation.weak (C := l21) d150 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l21 l151 [[(({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), true)], [(({(0, 0), (2, 0)} : Finset VV), true)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d152 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p152 :=
  IsLinDerivation.weak (C := l54) d151 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (weak_cert l54 l152 [[(({(0, 0), (2, 0)} : Finset VV), false), (({(0, 0), (1, 0)} : Finset VV), false)], [(({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), true), (({(0, 0), (2, 0)} : Finset VV), false), (({(0, 1), (1, 1)} : Finset VV), false)]] (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d153 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p153 :=
  IsLinDerivation.res (C := l152) (D := l151) d152 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨({(0, 0), (2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d154 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p154 :=
  IsLinDerivation.res (C := l150) (D := l153) d153 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) ⟨({(0, 0), (0, 1), (2, 0), (2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d155 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p155 :=
  IsLinDerivation.res (C := l154) (D := l137) d154 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))) ⟨({(0, 1), (1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d156 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p156 :=
  IsLinDerivation.res (C := l123) (D := l10) d155 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ⟨({(0, 1), (1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d157 : IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) p157 :=
  IsLinDerivation.res (C := l155) (D := l156) d156 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({(0, 0), (1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem main_aux : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 2)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP 5 2) π ∧ π.length ≤ 158 :=
  ⟨p157, ⟨d157, List.Mem.head _⟩, by decide +kernel⟩

end PEqualNP.Outside.L_pcx_137

theorem PEqualNP.Outside.L_pcx_137 : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 2)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP 5 2) π ∧ π.length ≤ 158 :=
  PEqualNP.Outside.L_pcx_137.main_aux
