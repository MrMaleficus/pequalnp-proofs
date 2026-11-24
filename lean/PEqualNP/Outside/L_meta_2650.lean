import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2650

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def val (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [val g w]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [val g w]) := rfl

theorem eval_run (C : Circuit) (y : List Bool) :
    C.eval y = (run C.gates y).getD C.output false := rfl

def rn (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def gor (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩

def rr (p : List ℕ) (i : ℕ) : ℕ := if i < 14 then p.getD i 0 else i

def yy (p : List ℕ) (x : Fin 14 → Bool) : Fin 14 → Bool :=
  fun k => (List.ofFn x).getD (p.getD k 0) false

def E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def tab : List (ℕ × ℕ × List ℕ × List ℕ) := [
  (0, 1, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
  (0, 2, [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13], [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13]),
  (0, 3, [0, 3, 2, 1, 5, 4, 6, 7, 8, 11, 10, 9, 13, 12], [0, 3, 2, 1, 5, 4, 6, 7, 8, 11, 10, 9, 13, 12]),
  (0, 4, [0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13], [0, 4, 1, 5, 2, 6, 3, 10, 7, 11, 8, 12, 9, 13]),
  (0, 5, [0, 2, 5, 6, 3, 1, 4, 8, 10, 13, 7, 11, 9, 12], [0, 5, 1, 4, 6, 2, 3, 10, 7, 12, 8, 11, 13, 9]),
  (0, 6, [0, 2, 3, 6, 5, 4, 1, 8, 7, 13, 10, 9, 11, 12], [0, 6, 1, 2, 5, 4, 3, 8, 7, 11, 10, 12, 13, 9]),
  (0, 7, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
  (0, 8, [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13], [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13]),
  (0, 9, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
  (0, 10, [0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13], [0, 4, 1, 5, 2, 6, 3, 10, 7, 11, 8, 12, 9, 13]),
  (0, 11, [0, 2, 3, 6, 5, 4, 1, 8, 7, 13, 10, 9, 11, 12], [0, 6, 1, 2, 5, 4, 3, 8, 7, 11, 10, 12, 13, 9]),
  (0, 12, [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13], [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13]),
  (0, 13, [0, 1, 5, 3, 6, 2, 4, 7, 10, 13, 8, 11, 12, 9], [0, 1, 5, 3, 6, 2, 4, 7, 10, 13, 8, 11, 12, 9]),
  (1, 0, [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8], [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8]),
  (1, 2, [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7], [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8]),
  (1, 3, [3, 0, 2, 1, 6, 4, 5, 7, 12, 10, 11, 9, 13, 8], [1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12]),
  (1, 4, [2, 0, 3, 6, 1, 4, 5, 8, 12, 10, 13, 9, 11, 7], [1, 4, 0, 2, 5, 6, 3, 13, 7, 11, 9, 12, 8, 10]),
  (1, 5, [2, 0, 5, 6, 4, 1, 3, 8, 12, 7, 13, 11, 9, 10], [1, 5, 0, 6, 4, 2, 3, 9, 7, 12, 13, 11, 8, 10]),
  (1, 6, [2, 0, 4, 6, 5, 3, 1, 8, 13, 7, 12, 9, 11, 10], [1, 6, 0, 5, 2, 4, 3, 9, 7, 11, 13, 12, 10, 8]),
  (1, 7, [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8], [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8]),
  (1, 8, [1, 0, 5, 3, 4, 2, 6, 7, 9, 8, 13, 11, 12, 10], [1, 0, 5, 3, 4, 2, 6, 7, 9, 8, 13, 11, 12, 10]),
  (1, 9, [2, 0, 4, 6, 5, 3, 1, 8, 13, 7, 12, 9, 11, 10], [1, 6, 0, 5, 2, 4, 3, 9, 7, 11, 13, 12, 10, 8]),
  (1, 10, [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8], [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8]),
  (1, 11, [2, 0, 3, 6, 1, 4, 5, 8, 12, 10, 13, 9, 11, 7], [1, 4, 0, 2, 5, 6, 3, 13, 7, 11, 9, 12, 8, 10]),
  (1, 12, [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7], [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8]),
  (1, 13, [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7], [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8]),
  (2, 0, [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8], [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7]),
  (2, 1, [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7], [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7]),
  (2, 3, [2, 4, 0, 1, 5, 3, 6, 13, 8, 11, 12, 9, 7, 10], [2, 3, 0, 5, 1, 4, 6, 12, 8, 11, 13, 9, 10, 7]),
  (2, 4, [2, 3, 0, 5, 1, 4, 6, 12, 8, 11, 13, 9, 10, 7], [2, 4, 0, 1, 5, 3, 6, 13, 8, 11, 12, 9, 7, 10]),
  (2, 5, [2, 5, 0, 3, 4, 1, 6, 12, 8, 9, 13, 11, 7, 10], [2, 5, 0, 3, 4, 1, 6, 12, 8, 9, 13, 11, 7, 10]),
  (2, 6, [3, 2, 0, 5, 6, 4, 1, 12, 7, 13, 11, 9, 10, 8], [2, 6, 1, 0, 5, 3, 4, 8, 13, 11, 12, 10, 7, 9]),
  (2, 7, [1, 5, 0, 6, 4, 2, 3, 9, 7, 12, 13, 11, 8, 10], [2, 0, 5, 6, 4, 1, 3, 8, 12, 7, 13, 11, 9, 10]),
  (2, 8, [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8], [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7]),
  (2, 9, [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7], [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7]),
  (2, 10, [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8], [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7]),
  (2, 11, [2, 3, 0, 5, 1, 4, 6, 12, 8, 11, 13, 9, 10, 7], [2, 4, 0, 1, 5, 3, 6, 13, 8, 11, 12, 9, 7, 10]),
  (2, 12, [2, 4, 0, 1, 5, 3, 6, 13, 8, 11, 12, 9, 7, 10], [2, 3, 0, 5, 1, 4, 6, 12, 8, 11, 13, 9, 10, 7]),
  (2, 13, [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7], [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7]),
  (3, 0, [1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12], [3, 0, 2, 1, 6, 4, 5, 7, 12, 10, 11, 9, 13, 8]),
  (3, 1, [3, 1, 2, 0, 4, 6, 5, 7, 12, 9, 11, 10, 8, 13], [3, 1, 2, 0, 4, 6, 5, 7, 12, 9, 11, 10, 8, 13]),
  (3, 2, [2, 6, 1, 0, 5, 3, 4, 8, 13, 11, 12, 10, 7, 9], [3, 2, 0, 5, 6, 4, 1, 12, 7, 13, 11, 9, 10, 8]),
  (3, 4, [2, 6, 5, 0, 1, 4, 3, 8, 12, 11, 13, 7, 10, 9], [3, 4, 0, 6, 5, 2, 1, 11, 7, 13, 12, 9, 8, 10]),
  (3, 5, [2, 6, 3, 0, 4, 1, 5, 8, 12, 9, 13, 10, 7, 11], [3, 5, 0, 2, 4, 6, 1, 12, 7, 9, 11, 13, 8, 10]),
  (3, 6, [2, 6, 4, 0, 3, 5, 1, 8, 13, 9, 12, 7, 10, 11], [3, 6, 0, 4, 2, 5, 1, 11, 7, 9, 12, 13, 10, 8]),
  (3, 7, [1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12], [3, 0, 2, 1, 6, 4, 5, 7, 12, 10, 11, 9, 13, 8]),
  (3, 8, [1, 3, 5, 0, 2, 4, 6, 7, 9, 11, 13, 8, 10, 12], [3, 0, 4, 1, 5, 2, 6, 7, 11, 8, 12, 9, 13, 10]),
  (3, 9, [2, 6, 3, 0, 4, 1, 5, 8, 12, 9, 13, 10, 7, 11], [3, 5, 0, 2, 4, 6, 1, 12, 7, 9, 11, 13, 8, 10]),
  (3, 10, [1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12], [3, 0, 2, 1, 6, 4, 5, 7, 12, 10, 11, 9, 13, 8]),
  (3, 11, [2, 6, 4, 0, 3, 5, 1, 8, 13, 9, 12, 7, 10, 11], [3, 6, 0, 4, 2, 5, 1, 11, 7, 9, 12, 13, 10, 8]),
  (3, 12, [2, 6, 1, 0, 5, 3, 4, 8, 13, 11, 12, 10, 7, 9], [3, 2, 0, 5, 6, 4, 1, 12, 7, 13, 11, 9, 10, 8]),
  (3, 13, [2, 6, 1, 0, 5, 3, 4, 8, 13, 11, 12, 10, 7, 9], [3, 2, 0, 5, 6, 4, 1, 12, 7, 13, 11, 9, 10, 8]),
  (4, 0, [1, 2, 6, 4, 0, 3, 5, 13, 9, 12, 7, 10, 11, 8], [4, 0, 1, 5, 3, 6, 2, 10, 13, 8, 11, 12, 9, 7]),
  (4, 1, [2, 1, 3, 4, 0, 6, 5, 13, 12, 9, 8, 10, 11, 7], [4, 1, 0, 2, 3, 6, 5, 13, 10, 9, 11, 12, 8, 7]),
  (4, 2, [2, 3, 1, 5, 0, 6, 4, 12, 13, 11, 8, 10, 9, 7], [4, 2, 0, 1, 6, 3, 5, 13, 10, 12, 11, 9, 7, 8]),
  (4, 3, [2, 4, 5, 1, 0, 6, 3, 13, 12, 11, 8, 7, 9, 10], [4, 3, 0, 6, 1, 2, 5, 11, 10, 12, 13, 9, 8, 7]),
  (4, 5, [3, 2, 6, 5, 0, 1, 4, 12, 11, 13, 7, 10, 9, 8], [4, 5, 1, 0, 6, 3, 2, 10, 13, 12, 11, 8, 7, 9]),
  (4, 6, [2, 5, 4, 3, 0, 6, 1, 12, 13, 9, 8, 7, 11, 10], [4, 6, 0, 3, 2, 1, 5, 11, 10, 9, 13, 12, 7, 8]),
  (4, 7, [1, 5, 4, 6, 0, 3, 2, 9, 13, 12, 7, 8, 11, 10], [4, 0, 6, 5, 2, 1, 3, 10, 11, 7, 13, 12, 9, 8]),
  (4, 8, [1, 2, 6, 4, 0, 3, 5, 13, 9, 12, 7, 10, 11, 8], [4, 0, 1, 5, 3, 6, 2, 10, 13, 8, 11, 12, 9, 7]),
  (4, 9, [2, 1, 3, 4, 0, 6, 5, 13, 12, 9, 8, 10, 11, 7], [4, 1, 0, 2, 3, 6, 5, 13, 10, 9, 11, 12, 8, 7]),
  (4, 10, [1, 2, 6, 4, 0, 3, 5, 13, 9, 12, 7, 10, 11, 8], [4, 0, 1, 5, 3, 6, 2, 10, 13, 8, 11, 12, 9, 7]),
  (4, 11, [2, 4, 5, 1, 0, 6, 3, 13, 12, 11, 8, 7, 9, 10], [4, 3, 0, 6, 1, 2, 5, 11, 10, 12, 13, 9, 8, 7]),
  (4, 12, [2, 3, 1, 5, 0, 6, 4, 12, 13, 11, 8, 10, 9, 7], [4, 2, 0, 1, 6, 3, 5, 13, 10, 12, 11, 9, 7, 8]),
  (4, 13, [2, 1, 3, 4, 0, 6, 5, 13, 12, 9, 8, 10, 11, 7], [4, 1, 0, 2, 3, 6, 5, 13, 10, 9, 11, 12, 8, 7]),
  (5, 0, [1, 2, 5, 4, 3, 0, 6, 13, 9, 8, 7, 11, 10, 12], [5, 0, 1, 4, 3, 2, 6, 10, 9, 8, 12, 11, 13, 7]),
  (5, 1, [2, 1, 5, 4, 6, 0, 3, 13, 12, 7, 8, 11, 10, 9], [5, 1, 0, 6, 3, 2, 4, 9, 10, 13, 12, 11, 8, 7]),
  (5, 2, [2, 5, 1, 3, 6, 0, 4, 12, 13, 10, 8, 11, 7, 9], [5, 2, 0, 3, 6, 1, 4, 12, 10, 13, 9, 11, 7, 8]),
  (5, 3, [2, 4, 3, 1, 6, 0, 5, 13, 12, 10, 8, 9, 7, 11], [5, 3, 0, 2, 1, 6, 4, 12, 10, 11, 9, 13, 8, 7]),
  (5, 4, [3, 2, 4, 5, 1, 0, 6, 12, 11, 8, 7, 9, 10, 13], [5, 4, 1, 0, 2, 3, 6, 10, 9, 11, 12, 8, 7, 13]),
  (5, 6, [2, 3, 4, 5, 6, 0, 1, 12, 13, 7, 8, 9, 10, 11], [5, 6, 0, 1, 2, 3, 4, 9, 10, 11, 12, 13, 7, 8]),
  (5, 7, [1, 5, 2, 6, 3, 0, 4, 9, 13, 10, 7, 11, 8, 12], [5, 0, 2, 4, 6, 1, 3, 10, 12, 7, 9, 11, 13, 8]),
  (5, 8, [1, 2, 5, 4, 3, 0, 6, 13, 9, 8, 7, 11, 10, 12], [5, 0, 1, 4, 3, 2, 6, 10, 9, 8, 12, 11, 13, 7]),
  (5, 9, [2, 1, 5, 4, 6, 0, 3, 13, 12, 7, 8, 11, 10, 9], [5, 1, 0, 6, 3, 2, 4, 9, 10, 13, 12, 11, 8, 7]),
  (5, 10, [1, 2, 5, 4, 3, 0, 6, 13, 9, 8, 7, 11, 10, 12], [5, 0, 1, 4, 3, 2, 6, 10, 9, 8, 12, 11, 13, 7]),
  (5, 11, [2, 3, 4, 5, 6, 0, 1, 12, 13, 7, 8, 9, 10, 11], [5, 6, 0, 1, 2, 3, 4, 9, 10, 11, 12, 13, 7, 8]),
  (5, 12, [2, 4, 3, 1, 6, 0, 5, 13, 12, 10, 8, 9, 7, 11], [5, 3, 0, 2, 1, 6, 4, 12, 10, 11, 9, 13, 8, 7]),
  (5, 13, [2, 1, 5, 4, 6, 0, 3, 13, 12, 7, 8, 11, 10, 9], [5, 1, 0, 6, 3, 2, 4, 9, 10, 13, 12, 11, 8, 7]),
  (6, 0, [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12], [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7]),
  (6, 1, [2, 1, 6, 4, 5, 3, 0, 13, 8, 7, 12, 10, 11, 9], [6, 1, 0, 5, 3, 4, 2, 9, 8, 13, 11, 12, 10, 7]),
  (6, 2, [3, 2, 1, 5, 4, 6, 0, 12, 7, 8, 11, 10, 9, 13], [6, 2, 1, 0, 4, 3, 5, 8, 9, 12, 11, 10, 7, 13]),
  (6, 3, [2, 4, 6, 1, 3, 5, 0, 13, 8, 10, 12, 7, 9, 11], [6, 3, 0, 4, 1, 5, 2, 11, 8, 12, 9, 13, 10, 7]),
  (6, 4, [2, 5, 6, 3, 1, 4, 0, 12, 8, 10, 13, 7, 11, 9], [6, 4, 0, 3, 5, 1, 2, 11, 8, 13, 9, 12, 7, 10]),
  (6, 5, [2, 3, 6, 5, 4, 1, 0, 12, 8, 7, 13, 10, 9, 11], [6, 5, 0, 1, 4, 3, 2, 9, 8, 12, 11, 13, 7, 10]),
  (6, 7, [1, 5, 3, 6, 2, 4, 0, 9, 7, 10, 13, 8, 11, 12], [6, 0, 4, 2, 5, 1, 3, 8, 11, 7, 9, 12, 13, 10]),
  (6, 8, [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12], [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7]),
  (6, 9, [2, 1, 6, 4, 5, 3, 0, 13, 8, 7, 12, 10, 11, 9], [6, 1, 0, 5, 3, 4, 2, 9, 8, 13, 11, 12, 10, 7]),
  (6, 10, [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12], [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7]),
  (6, 11, [2, 4, 6, 1, 3, 5, 0, 13, 8, 10, 12, 7, 9, 11], [6, 3, 0, 4, 1, 5, 2, 11, 8, 12, 9, 13, 10, 7]),
  (6, 12, [2, 3, 6, 5, 4, 1, 0, 12, 8, 7, 13, 10, 9, 11], [6, 5, 0, 1, 4, 3, 2, 9, 8, 12, 11, 13, 7, 10]),
  (6, 13, [2, 1, 6, 4, 5, 3, 0, 13, 8, 7, 12, 10, 11, 9], [6, 1, 0, 5, 3, 4, 2, 9, 8, 13, 11, 12, 10, 7]),
  (7, 0, [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6], [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6]),
  (7, 1, [8, 7, 9, 10, 13, 12, 11, 0, 6, 3, 2, 4, 5, 1], [7, 13, 10, 9, 11, 12, 8, 1, 0, 2, 3, 6, 5, 4]),
  (7, 2, [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6], [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6]),
  (7, 3, [8, 10, 9, 7, 12, 13, 11, 0, 6, 4, 2, 3, 1, 5], [7, 12, 10, 11, 9, 13, 8, 3, 0, 2, 1, 6, 4, 5]),
  (7, 4, [7, 8, 11, 10, 9, 13, 12, 0, 3, 2, 1, 5, 4, 6], [7, 10, 9, 8, 12, 11, 13, 0, 1, 4, 3, 2, 6, 5]),
  (7, 5, [7, 8, 12, 10, 13, 9, 11, 0, 3, 6, 1, 4, 5, 2], [7, 10, 13, 8, 11, 12, 9, 0, 1, 5, 3, 6, 2, 4]),
  (7, 6, [7, 8, 13, 10, 12, 11, 9, 0, 1, 6, 3, 5, 4, 2], [7, 8, 13, 10, 12, 11, 9, 0, 1, 6, 3, 5, 4, 2]),
  (7, 8, [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6], [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6]),
  (7, 9, [8, 7, 11, 10, 12, 13, 9, 0, 6, 1, 2, 5, 4, 3], [7, 9, 10, 13, 12, 11, 8, 1, 0, 6, 3, 2, 4, 5]),
  (7, 10, [7, 8, 11, 10, 9, 13, 12, 0, 3, 2, 1, 5, 4, 6], [7, 10, 9, 8, 12, 11, 13, 0, 1, 4, 3, 2, 6, 5]),
  (7, 11, [8, 10, 11, 7, 13, 12, 9, 0, 6, 5, 2, 1, 3, 4], [7, 11, 10, 12, 13, 9, 8, 3, 0, 6, 1, 2, 5, 4]),
  (7, 12, [8, 10, 9, 7, 12, 13, 11, 0, 6, 4, 2, 3, 1, 5], [7, 12, 10, 11, 9, 13, 8, 3, 0, 2, 1, 6, 4, 5]),
  (7, 13, [8, 7, 9, 10, 13, 12, 11, 0, 6, 3, 2, 4, 5, 1], [7, 13, 10, 9, 11, 12, 8, 1, 0, 2, 3, 6, 5, 4]),
  (8, 0, [7, 9, 8, 13, 11, 12, 10, 1, 0, 5, 3, 4, 2, 6], [8, 7, 12, 10, 11, 9, 13, 0, 2, 1, 6, 4, 5, 3]),
  (8, 1, [7, 9, 8, 13, 11, 12, 10, 1, 0, 5, 3, 4, 2, 6], [8, 7, 12, 10, 11, 9, 13, 0, 2, 1, 6, 4, 5, 3]),
  (8, 2, [8, 9, 7, 11, 13, 12, 10, 6, 0, 5, 2, 4, 3, 1], [8, 13, 10, 12, 11, 9, 7, 2, 0, 1, 6, 3, 5, 4]),
  (8, 3, [7, 13, 8, 9, 12, 11, 10, 1, 0, 4, 3, 5, 6, 2], [8, 7, 13, 10, 9, 11, 12, 0, 2, 3, 6, 5, 4, 1]),
  (8, 4, [7, 11, 8, 12, 9, 13, 10, 3, 0, 4, 1, 5, 2, 6], [8, 10, 12, 7, 9, 11, 13, 0, 2, 4, 6, 1, 3, 5]),
  (8, 5, [7, 11, 10, 12, 13, 9, 8, 3, 0, 6, 1, 2, 5, 4], [8, 10, 11, 7, 13, 12, 9, 0, 6, 5, 2, 1, 3, 4]),
  (8, 6, [8, 9, 10, 11, 12, 13, 7, 6, 0, 1, 2, 3, 4, 5], [8, 9, 10, 11, 12, 13, 7, 6, 0, 1, 2, 3, 4, 5]),
  (8, 7, [7, 9, 8, 13, 11, 12, 10, 1, 0, 5, 3, 4, 2, 6], [8, 7, 12, 10, 11, 9, 13, 0, 2, 1, 6, 4, 5, 3]),
  (8, 9, [8, 9, 10, 11, 12, 13, 7, 6, 0, 1, 2, 3, 4, 5], [8, 9, 10, 11, 12, 13, 7, 6, 0, 1, 2, 3, 4, 5]),
  (8, 10, [7, 11, 8, 12, 9, 13, 10, 3, 0, 4, 1, 5, 2, 6], [8, 10, 12, 7, 9, 11, 13, 0, 2, 4, 6, 1, 3, 5]),
  (8, 11, [8, 11, 10, 9, 13, 12, 7, 6, 0, 3, 2, 1, 5, 4], [8, 11, 10, 9, 13, 12, 7, 6, 0, 3, 2, 1, 5, 4]),
  (8, 12, [8, 11, 7, 9, 12, 13, 10, 6, 0, 4, 2, 5, 1, 3], [8, 12, 10, 13, 9, 11, 7, 2, 0, 3, 6, 1, 4, 5]),
  (8, 13, [8, 9, 7, 11, 13, 12, 10, 6, 0, 5, 2, 4, 3, 1], [8, 13, 10, 12, 11, 9, 7, 2, 0, 1, 6, 3, 5, 4]),
  (9, 0, [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3], [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3]),
  (9, 1, [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3], [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3]),
  (9, 2, [11, 7, 9, 12, 13, 10, 8, 3, 6, 0, 4, 2, 5, 1], [9, 13, 11, 7, 10, 12, 8, 1, 6, 2, 5, 0, 3, 4]),
  (9, 3, [11, 8, 12, 9, 13, 10, 7, 6, 3, 0, 4, 1, 5, 2], [9, 11, 13, 8, 10, 12, 7, 6, 1, 3, 5, 0, 2, 4]),
  (9, 4, [11, 7, 13, 12, 9, 8, 10, 3, 4, 0, 6, 5, 2, 1], [9, 13, 12, 7, 8, 11, 10, 1, 5, 4, 6, 0, 3, 2]),
  (9, 5, [9, 8, 12, 11, 13, 7, 10, 6, 5, 0, 1, 4, 3, 2], [9, 10, 13, 12, 11, 8, 7, 5, 1, 0, 6, 3, 2, 4]),
  (9, 6, [9, 8, 13, 11, 12, 10, 7, 6, 1, 0, 5, 3, 4, 2], [9, 8, 13, 11, 12, 10, 7, 6, 1, 0, 5, 3, 4, 2]),
  (9, 7, [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3], [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3]),
  (9, 8, [9, 8, 13, 11, 12, 10, 7, 6, 1, 0, 5, 3, 4, 2], [9, 8, 13, 11, 12, 10, 7, 6, 1, 0, 5, 3, 4, 2]),
  (9, 10, [9, 8, 12, 11, 13, 7, 10, 6, 5, 0, 1, 4, 3, 2], [9, 10, 13, 12, 11, 8, 7, 5, 1, 0, 6, 3, 2, 4]),
  (9, 11, [11, 8, 12, 9, 13, 10, 7, 6, 3, 0, 4, 1, 5, 2], [9, 11, 13, 8, 10, 12, 7, 6, 1, 3, 5, 0, 2, 4]),
  (9, 12, [11, 8, 13, 9, 12, 7, 10, 6, 4, 0, 3, 5, 1, 2], [9, 12, 13, 10, 8, 11, 7, 5, 1, 3, 6, 0, 4, 2]),
  (9, 13, [11, 7, 9, 12, 13, 10, 8, 3, 6, 0, 4, 2, 5, 1], [9, 13, 11, 7, 10, 12, 8, 1, 6, 2, 5, 0, 3, 4]),
  (10, 0, [7, 9, 11, 13, 8, 10, 12, 1, 3, 5, 0, 2, 4, 6], [10, 7, 11, 8, 12, 9, 13, 0, 4, 1, 5, 2, 6, 3]),
  (10, 1, [7, 9, 11, 13, 8, 10, 12, 1, 3, 5, 0, 2, 4, 6], [10, 7, 11, 8, 12, 9, 13, 0, 4, 1, 5, 2, 6, 3]),
  (10, 2, [7, 11, 9, 12, 8, 10, 13, 3, 1, 4, 0, 2, 5, 6], [10, 8, 11, 7, 9, 12, 13, 0, 4, 2, 5, 1, 3, 6]),
  (10, 3, [7, 13, 11, 9, 10, 8, 12, 1, 3, 2, 0, 5, 6, 4], [10, 7, 9, 8, 13, 11, 12, 0, 5, 3, 4, 2, 6, 1]),
  (10, 4, [8, 9, 13, 11, 7, 10, 12, 6, 2, 5, 0, 3, 4, 1], [10, 13, 8, 11, 12, 9, 7, 4, 0, 1, 5, 3, 6, 2]),
  (10, 5, [8, 9, 12, 11, 10, 7, 13, 6, 2, 1, 0, 4, 3, 5], [10, 9, 8, 12, 11, 13, 7, 5, 0, 1, 4, 3, 2, 6]),
  (10, 6, [7, 11, 13, 12, 10, 8, 9, 3, 1, 6, 0, 5, 2, 4], [10, 8, 12, 7, 13, 11, 9, 0, 5, 6, 4, 1, 3, 2]),
  (10, 7, [7, 9, 11, 13, 8, 10, 12, 1, 3, 5, 0, 2, 4, 6], [10, 7, 11, 8, 12, 9, 13, 0, 4, 1, 5, 2, 6, 3]),
  (10, 8, [7, 11, 9, 12, 8, 10, 13, 3, 1, 4, 0, 2, 5, 6], [10, 8, 11, 7, 9, 12, 13, 0, 4, 2, 5, 1, 3, 6]),
  (10, 9, [8, 9, 12, 11, 10, 7, 13, 6, 2, 1, 0, 4, 3, 5], [10, 9, 8, 12, 11, 13, 7, 5, 0, 1, 4, 3, 2, 6]),
  (10, 11, [8, 11, 12, 9, 7, 10, 13, 6, 2, 4, 0, 1, 5, 3], [10, 11, 8, 13, 9, 12, 7, 4, 0, 3, 5, 1, 2, 6]),
  (10, 12, [8, 11, 13, 9, 10, 7, 12, 6, 2, 3, 0, 5, 1, 4], [10, 12, 8, 9, 13, 11, 7, 5, 0, 3, 4, 1, 6, 2]),
  (10, 13, [8, 9, 13, 11, 7, 10, 12, 6, 2, 5, 0, 3, 4, 1], [10, 13, 8, 11, 12, 9, 7, 4, 0, 1, 5, 3, 6, 2]),
  (11, 0, [9, 11, 12, 8, 7, 13, 10, 6, 5, 4, 1, 0, 2, 3], [11, 10, 12, 13, 9, 8, 7, 4, 3, 0, 6, 1, 2, 5]),
  (11, 1, [11, 9, 12, 8, 10, 13, 7, 6, 3, 1, 4, 0, 2, 5], [11, 9, 12, 8, 10, 13, 7, 6, 3, 1, 4, 0, 2, 5]),
  (11, 2, [11, 12, 9, 7, 10, 13, 8, 3, 6, 2, 4, 0, 1, 5], [11, 12, 9, 7, 10, 13, 8, 3, 6, 2, 4, 0, 1, 5]),
  (11, 3, [9, 13, 11, 7, 10, 12, 8, 1, 6, 2, 5, 0, 3, 4], [11, 7, 9, 12, 13, 10, 8, 3, 6, 0, 4, 2, 5, 1]),
  (11, 4, [9, 11, 12, 8, 7, 13, 10, 6, 5, 4, 1, 0, 2, 3], [11, 10, 12, 13, 9, 8, 7, 4, 3, 0, 6, 1, 2, 5]),
  (11, 5, [11, 12, 13, 7, 8, 9, 10, 3, 4, 5, 6, 0, 1, 2], [11, 12, 13, 7, 8, 9, 10, 3, 4, 5, 6, 0, 1, 2]),
  (11, 6, [9, 11, 13, 8, 10, 12, 7, 6, 1, 3, 5, 0, 2, 4], [11, 8, 12, 9, 13, 10, 7, 6, 3, 0, 4, 1, 5, 2]),
  (11, 7, [9, 13, 11, 7, 10, 12, 8, 1, 6, 2, 5, 0, 3, 4], [11, 7, 9, 12, 13, 10, 8, 3, 6, 0, 4, 2, 5, 1]),
  (11, 8, [9, 11, 13, 8, 10, 12, 7, 6, 1, 3, 5, 0, 2, 4], [11, 8, 12, 9, 13, 10, 7, 6, 3, 0, 4, 1, 5, 2]),
  (11, 9, [11, 9, 12, 8, 10, 13, 7, 6, 3, 1, 4, 0, 2, 5], [11, 9, 12, 8, 10, 13, 7, 6, 3, 1, 4, 0, 2, 5]),
  (11, 10, [9, 11, 12, 8, 7, 13, 10, 6, 5, 4, 1, 0, 2, 3], [11, 10, 12, 13, 9, 8, 7, 4, 3, 0, 6, 1, 2, 5]),
  (11, 12, [11, 12, 9, 7, 10, 13, 8, 3, 6, 2, 4, 0, 1, 5], [11, 12, 9, 7, 10, 13, 8, 3, 6, 2, 4, 0, 1, 5]),
  (11, 13, [11, 9, 13, 8, 7, 12, 10, 6, 4, 5, 3, 0, 2, 1], [11, 13, 12, 10, 8, 9, 7, 4, 3, 1, 6, 0, 5, 2]),
  (12, 0, [9, 11, 7, 8, 12, 10, 13, 6, 1, 4, 5, 2, 0, 3], [12, 8, 11, 13, 9, 10, 7, 2, 3, 0, 5, 1, 4, 6]),
  (12, 1, [11, 9, 7, 8, 13, 10, 12, 6, 3, 5, 4, 2, 0, 1], [12, 13, 11, 8, 10, 9, 7, 2, 3, 1, 5, 0, 6, 4]),
  (12, 2, [9, 11, 7, 8, 12, 10, 13, 6, 1, 4, 5, 2, 0, 3], [12, 8, 11, 13, 9, 10, 7, 2, 3, 0, 5, 1, 4, 6]),
  (12, 3, [9, 13, 8, 7, 12, 10, 11, 1, 6, 4, 5, 3, 0, 2], [12, 7, 13, 11, 9, 10, 8, 3, 2, 0, 5, 6, 4, 1]),
  (12, 4, [11, 12, 10, 7, 9, 8, 13, 3, 4, 2, 6, 1, 0, 5], [12, 11, 9, 7, 8, 13, 10, 3, 5, 4, 2, 0, 1, 6]),
  (12, 5, [9, 11, 10, 8, 13, 7, 12, 6, 5, 3, 1, 2, 0, 4], [12, 10, 11, 9, 13, 8, 7, 5, 3, 0, 2, 1, 6, 4]),
  (12, 6, [11, 12, 8, 7, 13, 10, 9, 3, 6, 5, 4, 1, 0, 2], [12, 11, 13, 7, 10, 9, 8, 3, 2, 6, 5, 0, 1, 4]),
  (12, 7, [9, 13, 8, 7, 12, 10, 11, 1, 6, 4, 5, 3, 0, 2], [12, 7, 13, 11, 9, 10, 8, 3, 2, 0, 5, 6, 4, 1]),
  (12, 8, [9, 11, 7, 8, 12, 10, 13, 6, 1, 4, 5, 2, 0, 3], [12, 8, 11, 13, 9, 10, 7, 2, 3, 0, 5, 1, 4, 6]),
  (12, 9, [11, 9, 10, 8, 12, 7, 13, 6, 4, 1, 3, 2, 0, 5], [12, 9, 11, 10, 8, 13, 7, 5, 3, 1, 2, 0, 4, 6]),
  (12, 10, [9, 11, 10, 8, 13, 7, 12, 6, 5, 3, 1, 2, 0, 4], [12, 10, 11, 9, 13, 8, 7, 5, 3, 0, 2, 1, 6, 4]),
  (12, 11, [11, 12, 8, 7, 13, 10, 9, 3, 6, 5, 4, 1, 0, 2], [12, 11, 13, 7, 10, 9, 8, 3, 2, 6, 5, 0, 1, 4]),
  (12, 13, [11, 9, 7, 8, 13, 10, 12, 6, 3, 5, 4, 2, 0, 1], [12, 13, 11, 8, 10, 9, 7, 2, 3, 1, 5, 0, 6, 4]),
  (13, 0, [9, 7, 8, 13, 10, 12, 11, 1, 6, 3, 5, 4, 2, 0], [13, 7, 12, 9, 11, 10, 8, 1, 2, 0, 4, 6, 5, 3]),
  (13, 1, [9, 7, 8, 13, 10, 12, 11, 1, 6, 3, 5, 4, 2, 0], [13, 7, 12, 9, 11, 10, 8, 1, 2, 0, 4, 6, 5, 3]),
  (13, 2, [9, 8, 7, 11, 10, 12, 13, 6, 1, 2, 5, 4, 3, 0], [13, 8, 9, 12, 11, 10, 7, 2, 1, 0, 4, 3, 5, 6]),
  (13, 3, [11, 8, 7, 9, 10, 13, 12, 6, 3, 2, 4, 5, 1, 0], [13, 12, 9, 8, 10, 11, 7, 2, 1, 3, 4, 0, 6, 5]),
  (13, 4, [9, 8, 10, 11, 7, 13, 12, 6, 5, 2, 1, 3, 4, 0], [13, 10, 9, 11, 12, 8, 7, 4, 1, 0, 2, 3, 6, 5]),
  (13, 5, [11, 7, 10, 12, 8, 9, 13, 3, 4, 1, 6, 2, 5, 0], [13, 9, 11, 7, 8, 12, 10, 1, 4, 5, 2, 0, 3, 6]),
  (13, 6, [11, 7, 8, 12, 10, 13, 9, 3, 6, 1, 4, 5, 2, 0], [13, 9, 12, 7, 10, 11, 8, 1, 2, 6, 4, 0, 3, 5]),
  (13, 7, [9, 7, 8, 13, 10, 12, 11, 1, 6, 3, 5, 4, 2, 0], [13, 7, 12, 9, 11, 10, 8, 1, 2, 0, 4, 6, 5, 3]),
  (13, 8, [9, 8, 7, 11, 10, 12, 13, 6, 1, 2, 5, 4, 3, 0], [13, 8, 9, 12, 11, 10, 7, 2, 1, 0, 4, 3, 5, 6]),
  (13, 9, [11, 7, 8, 12, 10, 13, 9, 3, 6, 1, 4, 5, 2, 0], [13, 9, 12, 7, 10, 11, 8, 1, 2, 6, 4, 0, 3, 5]),
  (13, 10, [9, 8, 10, 11, 7, 13, 12, 6, 5, 2, 1, 3, 4, 0], [13, 10, 9, 11, 12, 8, 7, 4, 1, 0, 2, 3, 6, 5]),
  (13, 11, [11, 8, 10, 9, 7, 12, 13, 6, 4, 2, 3, 1, 5, 0], [13, 11, 9, 10, 8, 12, 7, 4, 1, 3, 2, 0, 5, 6]),
  (13, 12, [11, 8, 7, 9, 10, 13, 12, 6, 3, 2, 4, 5, 1, 0], [13, 12, 9, 8, 10, 11, 7, 2, 1, 3, 4, 0, 6, 5])]

abbrev Good (a b : ℕ) (p q : List ℕ) : Prop :=
  p.getD a 0 = 0 ∧ (p.getD b 0 = 1 ∨ p.getD b 0 = 7 ∨ p.getD b 0 = 9) ∧
  (∀ e ∈ E, (p.getD e.1 0, p.getD e.2 0) ∈ E ∨ (p.getD e.2 0, p.getD e.1 0) ∈ E) ∧
  (∀ e ∈ E, (q.getD e.1 0, q.getD e.2 0) ∈ E ∨ (q.getD e.2 0, q.getD e.1 0) ∈ E) ∧
  (∀ i ∈ List.range 14, p.getD (q.getD i 0) 0 = i ∧ q.getD i 0 < 14 ∧ p.getD i 0 < 14)

theorem tab_good : ∀ r ∈ tab, Good r.1 r.2.1 r.2.2.1 r.2.2.2 := by decide +kernel

theorem tab_cover : ∀ a ∈ List.range 14, ∀ b ∈ List.range 14, a ≠ b →
    ∃ r ∈ tab, r.1 = a ∧ r.2.1 = b := by decide +kernel

theorem rn_id (gs : List Gate) : gs.map (rn id) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, ih]
    cases g
    simp [rn]

theorem val_or (a b : ℕ) (y : List Bool) :
    val (gor a b) y = (y.getD a false || y.getD b false) := by
  simp [val, gor, GateOp.eval]

theorem getD_last (y : List Bool) (v : Bool) : (y ++ [v]).getD y.length false = v := by
  simp

theorem ofFn_getD (x : Fin 14 → Bool) (i : ℕ) (hi : i < 14) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  have h1 : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact hi
  rw [List.getD_eq_getElem _ _ h1, List.getElem_ofFn]

theorem bool_flow (t b b' c c' : Bool)
    (hb : b = t → b' = t) (hc : c = t → c' = t) :
    ((b && c) = t → (b' && c') = t) ∧ ((b || c) = t → (b' || c') = t) := by
  cases t <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

theorem gate_flow (t : Bool) (op : GateOp) (hop : op = .and ∨ op = .or)
    (ins : List ℕ) (p q : ℕ → Bool)
    (h : ∀ i, p i = t → q i = t) :
    op.eval (ins.map p) = t → op.eval (ins.map q) = t := by
  induction ins with
  | nil => exact id
  | cons i ins ih =>
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.all_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).1
    · simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).2

theorem flow (p q : ℕ → ℕ) (gs : List Gate) :
    ∀ (w v : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i k, k < gs.length → p i = w.length + k → q i = v.length + k) →
    (∀ i, w.getD (p i) false = true → v.getD (q i) false = true) →
    ∀ i, (run (gs.map (rn p)) w).getD (p i) false = true →
      (run (gs.map (rn q)) v).getD (q i) false = true := by
  induction gs with
  | nil =>
    intro w v _ _ hf i h
    exact hf i h
  | cons g gs ih =>
    intro w v hops hs hf i
    rw [List.map_cons, List.map_cons, run_cons, run_cons]
    have hstep : val (rn p g) w = true → val (rn q g) v = true := by
      have h0 := gate_flow true g.op (hops g List.mem_cons_self) g.inputs
        (fun i => w.getD (p i) false) (fun i => v.getD (q i) false) hf
      simpa only [val, rn, List.map_map, Function.comp_def] using h0
    refine ih (w ++ [val (rn p g) w]) (v ++ [val (rn q g) v])
      (fun a ha => hops a (List.mem_cons_of_mem _ ha)) ?_ ?_ i
    · intro j k hk hj
      rw [List.length_append, List.length_singleton] at hj ⊢
      have h0 := hs j (k + 1) (by rw [List.length_cons]; omega) (by omega)
      omega
    · intro j hj
      by_cases h1 : p j < w.length
      · rw [List.getD_append _ _ _ _ h1] at hj
        have h2 := hf j hj
        have h3 : q j < v.length := by
          by_contra hc
          rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hc)] at h2
          exact Bool.false_ne_true h2
        rw [List.getD_append _ _ _ _ h3]
        exact h2
      · by_cases h4 : p j = w.length
        · have h5 := hs j 0 (by rw [List.length_cons]; omega) (by omega)
          rw [h4, getD_last] at hj
          rw [h5, Nat.add_zero, getD_last]
          exact hstep hj
        · have h6 : (w ++ [val (rn p g) w]).length ≤ p j := by
            rw [List.length_append, List.length_singleton]
            omega
          rw [List.getD_eq_default _ _ h6] at hj
          exact absurd hj Bool.false_ne_true

theorem weq (p : List ℕ) (hp : ∀ i, i < 14 → p.getD i 0 < 14) (a b : ℕ) (ha : a < 14)
    (hb : b < 14) (x : Fin 14 → Bool) (j : Fin 14) (hpa : p.getD a 0 = 0)
    (hpb : p.getD b 0 = (j : ℕ)) (i : ℕ) :
    (List.ofFn (yy p x) ++ [val (gor a b) (List.ofFn (yy p x))]).getD i false
      = (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]).getD (rr p i) false := by
  have hy : (List.ofFn (yy p x)).length = 14 := List.length_ofFn
  have hx : (List.ofFn x).length = 14 := List.length_ofFn
  by_cases h1 : i < 14
  · have e0 : rr p i = p.getD i 0 := by unfold rr; rw [if_pos h1]
    have h2 : i < (List.ofFn (yy p x)).length := by omega
    have h3 : p.getD i 0 < (List.ofFn x).length := by rw [hx]; exact hp i h1
    rw [e0, List.getD_append _ _ _ _ h2, List.getD_append _ _ _ _ h3]
    exact ofFn_getD (yy p x) i h1
  · by_cases h2 : i = 14
    · have e1 : rr p i = 14 := by unfold rr; rw [if_neg h1]; exact h2
      have l1 := getD_last (List.ofFn (yy p x)) (val (gor a b) (List.ofFn (yy p x)))
      rw [hy] at l1
      have l2 := getD_last (List.ofFn x) (GateOp.or.eval [x 0, x j])
      rw [hx] at l2
      have e3 : (List.ofFn (yy p x)).getD a false = (List.ofFn x).getD 0 false := by
        have e4 : (List.ofFn (yy p x)).getD a false = (List.ofFn x).getD (p.getD a 0) false :=
          ofFn_getD (yy p x) a ha
        rw [e4, hpa]
      have e5 : (List.ofFn (yy p x)).getD b false = (List.ofFn x).getD (j : ℕ) false := by
        have e6 : (List.ofFn (yy p x)).getD b false = (List.ofFn x).getD (p.getD b 0) false :=
          ofFn_getD (yy p x) b hb
        rw [e6, hpb]
      have e7 : (List.ofFn x).getD 0 false = x 0 := ofFn_getD x 0 (by omega)
      have e8 : (List.ofFn x).getD (j : ℕ) false = x j := ofFn_getD x j j.isLt
      rw [e1, h2, l1, l2, val_or, e3, e5, e7, e8]
      simp [GateOp.eval]
    · have e2 : rr p i = i := by unfold rr; rw [if_neg h1]
      have h6 : (List.ofFn (yy p x) ++ [val (gor a b) (List.ofFn (yy p x))]).length ≤ i := by
        rw [List.length_append, List.length_singleton, hy]
        omega
      have h7 : (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]).length ≤ i := by
        rw [List.length_append, List.length_singleton, hx]
        omega
      rw [e2, List.getD_eq_default _ _ h6, List.getD_eq_default _ _ h7]

theorem evalpart (C : Circuit) (rest : List Gate) (a b : ℕ) (p : List ℕ)
    (hg : C.gates = gor a b :: rest) (ha : a < 14) (hb : b < 14)
    (hops : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hp : ∀ i, i < 14 → p.getD i 0 < 14) (x : Fin 14 → Bool) (j : Fin 14)
    (hpa : p.getD a 0 = 0) (hpb : p.getD b 0 = (j : ℕ)) :
    (Circuit.mk (rest.map (rn (rr p))) (rr p C.output)).eval
        (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]) = true ↔
      C.eval (List.ofFn (yy p x)) = true := by
  have hw := weq p hp a b ha hb x j hpa hpb
  have hWl : (List.ofFn (yy p x) ++ [val (gor a b) (List.ofFn (yy p x))]).length = 15 := by
    rw [List.length_append, List.length_singleton, List.length_ofFn]
  have hVl : (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]).length = 15 := by
    rw [List.length_append, List.length_singleton, List.length_ofFn]
  have hCe : C.eval (List.ofFn (yy p x)) =
      (run (rest.map (rn id))
        (List.ofFn (yy p x) ++ [val (gor a b) (List.ofFn (yy p x))])).getD C.output false := by
    rw [rn_id, eval_run, hg, run_cons]
  rw [hCe]
  constructor
  · intro h
    have h' : (run (rest.map (rn (rr p))) (List.ofFn x ++ [GateOp.or.eval [x 0, x j]])).getD
        (rr p C.output) false = true := h
    refine flow (rr p) id rest (List.ofFn x ++ [GateOp.or.eval [x 0, x j]])
      (List.ofFn (yy p x) ++ [val (gor a b) (List.ofFn (yy p x))]) hops ?_ ?_ C.output h'
    · intro i k hk hi
      rw [hVl] at hi
      rw [hWl]
      show i = 15 + k
      unfold rr at hi
      by_cases h1 : i < 14
      · rw [if_pos h1] at hi
        have h2 := hp i h1
        omega
      · rw [if_neg h1] at hi
        exact hi
    · intro i hi
      show (List.ofFn (yy p x) ++ [val (gor a b) (List.ofFn (yy p x))]).getD i false = true
      rw [hw i]
      exact hi
  · intro h
    have h' : (run (rest.map (rn id))
        (List.ofFn (yy p x) ++ [val (gor a b) (List.ofFn (yy p x))])).getD
        (id C.output) false = true := h
    show (run (rest.map (rn (rr p))) (List.ofFn x ++ [GateOp.or.eval [x 0, x j]])).getD
        (rr p C.output) false = true
    refine flow id (rr p) rest (List.ofFn (yy p x) ++ [val (gor a b) (List.ofFn (yy p x))])
      (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]) hops ?_ ?_ C.output h'
    · intro i k hk hi
      rw [hWl] at hi
      rw [hVl]
      have hi' : i = 15 + k := hi
      have h1 : ¬ i < 14 := by omega
      unfold rr
      rw [if_neg h1]
      exact hi'
    · intro i hi
      have hi' : (List.ofFn (yy p x) ++ [val (gor a b) (List.ofFn (yy p x))]).getD i false
          = true := hi
      rw [hw i] at hi'
      exact hi'

theorem fequiv (p q : List ℕ) (x : Fin 14 → Bool)
    (h3 : ∀ e ∈ E, (p.getD e.1 0, p.getD e.2 0) ∈ E ∨ (p.getD e.2 0, p.getD e.1 0) ∈ E)
    (h4 : ∀ e ∈ E, (q.getD e.1 0, q.getD e.2 0) ∈ E ∨ (q.getD e.2 0, q.getD e.1 0) ∈ E)
    (h5 : ∀ i ∈ List.range 14, p.getD (q.getD i 0) 0 = i ∧ q.getD i 0 < 14 ∧ p.getD i 0 < 14) :
    (∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ yy p x u = true ∧ yy p x v = true) ↔
    (∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ x u = true ∧ x v = true) := by
  have hp : ∀ i, i < 14 → p.getD i 0 < 14 := fun i hi => (h5 i (List.mem_range.2 hi)).2.2
  have hq : ∀ i, i < 14 → q.getD i 0 < 14 := fun i hi => (h5 i (List.mem_range.2 hi)).2.1
  have hpq : ∀ i, i < 14 → p.getD (q.getD i 0) 0 = i := fun i hi => (h5 i (List.mem_range.2 hi)).1
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu' : x ⟨p.getD u 0, hp u u.isLt⟩ = true :=
      (ofFn_getD x (p.getD u 0) (hp u u.isLt)).symm.trans hu
    have hv' : x ⟨p.getD v 0, hp v v.isLt⟩ = true :=
      (ofFn_getD x (p.getD v 0) (hp v v.isLt)).symm.trans hv
    rcases h3 ((u : ℕ), (v : ℕ)) huv with h | h
    · exact ⟨⟨p.getD u 0, hp u u.isLt⟩, ⟨p.getD v 0, hp v v.isLt⟩, h, hu', hv'⟩
    · exact ⟨⟨p.getD v 0, hp v v.isLt⟩, ⟨p.getD u 0, hp u u.isLt⟩, h, hv', hu'⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu' : yy p x ⟨q.getD u 0, hq u u.isLt⟩ = true := by
      show (List.ofFn x).getD (p.getD (q.getD u 0) 0) false = true
      rw [hpq u u.isLt]
      exact (ofFn_getD x u u.isLt).trans hu
    have hv' : yy p x ⟨q.getD v 0, hq v v.isLt⟩ = true := by
      show (List.ofFn x).getD (p.getD (q.getD v 0) 0) false = true
      rw [hpq v v.isLt]
      exact (ofFn_getD x v v.isLt).trans hv
    rcases h4 ((u : ℕ), (v : ℕ)) huv with h | h
    · exact ⟨⟨q.getD u 0, hq u u.isLt⟩, ⟨q.getD v 0, hq v v.isLt⟩, h, hu', hv'⟩
    · exact ⟨⟨q.getD v 0, hq v v.isLt⟩, ⟨q.getD u 0, hq u u.isLt⟩, h, hv', hu'⟩

theorem core (C : Circuit) (rest : List Gate) (a b : ℕ)
    (hg : C.gates = { op := GateOp.or, inputs := [a, b] : Gate } :: rest)
    (ha : a < 14) (hb : b < 14) (hab : a ≠ b) (hm : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ x u = true ∧ x v = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧
      ((∀ x : Fin 14 → Bool, D.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x 1]]) = true ↔
          ∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ x u = true ∧ x v = true) ∨
       (∀ x : Fin 14 → Bool, D.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x 7]]) = true ↔
          ∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ x u = true ∧ x v = true) ∨
       (∀ x : Fin 14 → Bool, D.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x 9]]) = true ↔
          ∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ x u = true ∧ x v = true)) := by
  have hg' : C.gates = gor a b :: rest := hg
  have hops : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hgm
    have h0 := (hm g (by rw [hg']; exact List.mem_cons_of_mem _ hgm)).1
    simpa using h0
  obtain ⟨r, hr, hra, hrb⟩ := tab_cover a (List.mem_range.2 ha) b (List.mem_range.2 hb) hab
  obtain ⟨h1, h2, h3, h4, h5⟩ := tab_good r hr
  rw [hra] at h1
  rw [hrb] at h2
  have hp : ∀ i, i < 14 → r.2.2.1.getD i 0 < 14 :=
    fun i hi => (h5 i (List.mem_range.2 hi)).2.2
  have key : ∀ (j : Fin 14), r.2.2.1.getD b 0 = (j : ℕ) → ∀ x : Fin 14 → Bool,
      (Circuit.mk (rest.map (rn (rr r.2.2.1))) (rr r.2.2.1 C.output)).eval
        (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]) = true ↔
      ∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ x u = true ∧ x v = true := by
    intro j hj x
    rw [evalpart C rest a b r.2.2.1 hg' ha hb hops hp x j h1 hj, hC (yy r.2.2.1 x)]
    exact fequiv r.2.2.1 r.2.2.2 x h3 h4 h5
  refine ⟨⟨rest.map (rn (rr r.2.2.1)), rr r.2.2.1 C.output⟩, ?_, ?_, ?_⟩
  · intro g hgm
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hgm
    have h6 := hm g1 (by rw [hg']; exact List.mem_cons_of_mem _ hg1)
    refine ⟨h6.1, ?_⟩
    show (g1.inputs.map (rr r.2.2.1)).length ≤ 2
    rw [List.length_map]
    exact h6.2
  · have h0 : (rest.map (rn (rr r.2.2.1))).length + 1 = C.gates.length := by
      rw [List.length_map, hg', List.length_cons]
    exact le_of_eq h0
  · rcases h2 with h | h | h
    · exact Or.inl (key 1 (h.trans (by decide)))
    · exact Or.inr (Or.inl (key 7 (h.trans (by decide))))
    · exact Or.inr (Or.inr (key 9 (h.trans (by decide))))

theorem main_aux : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (14 : ℕ)) => ∀ (x5 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x5 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 (0 : Fin (14 : ℕ)), x5 x4]]) = Bool.true ↔ x2 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x4.gates = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } :: x5 → x6 < (14 : ℕ) → x7 < (14 : ℕ) → x6 ≠ x7 → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x13 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x13) = Bool.true ↔ x2 x13) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ x14.size + (1 : ℕ) ≤ x4.size ∧ (x3 x14 (1 : Fin (14 : ℕ)) ∨ x3 x14 (7 : Fin (14 : ℕ)) ∨ x3 x14 (9 : Fin (14 : ℕ))) := by
  intro x1 x2 x3 x4 x5 x6 x7 h1 h2 h3 h4 h5 h6
  exact core x4 x5 x6 x7 h1 h2 h3 h4 h5 h6

end PEqualNP.Outside.L_meta_2650

theorem PEqualNP.Outside.L_meta_2650 : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (14 : ℕ)) => ∀ (x5 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x5 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 (0 : Fin (14 : ℕ)), x5 x4]]) = Bool.true ↔ x2 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x4.gates = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } :: x5 → x6 < (14 : ℕ) → x7 < (14 : ℕ) → x6 ≠ x7 → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x13 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x13) = Bool.true ↔ x2 x13) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ x14.size + (1 : ℕ) ≤ x4.size ∧ (x3 x14 (1 : Fin (14 : ℕ)) ∨ x3 x14 (7 : Fin (14 : ℕ)) ∨ x3 x14 (9 : Fin (14 : ℕ))) :=
  PEqualNP.Outside.L_meta_2650.main_aux
