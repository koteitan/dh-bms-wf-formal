/-
  Computable version of Definition 5.1 (BM4 expansion via parents/ancestors),
  used to cross-check the paper's reformulated rule against yaBMS (`bms -v4`).
  Arrays are lists of columns; each column is a list of row entries.
-/
import Mathlib

namespace BM4C

abbrev Mat := List (List ℕ)

def colv (A : Mat) (i k : ℕ) : ℕ := (A.getD i []).getD k 0

/-- Largest valid structural candidate `j < i` for row `k`, given the candidate test. -/
def parentOf (A : Mat) (cand : ℕ → ℕ → Bool) (k i : ℕ) : Option ℕ :=
  ((List.range i).filter (fun j => cand j i && decide (colv A j k < colv A i k))).getLast?

/-- Follow the parent function from `i`; `fuel` bounds the length (parents decrease). -/
def chain (par : ℕ → Option ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, i => match par i with
    | none => []
    | some j => j :: chain par f j

/-- Strict `k`-ancestors of `i` (as a list of positions). -/
def ancC (A : Mat) : ℕ → ℕ → List ℕ
  | 0 => fun i => chain (parentOf A (fun j i => decide (j < i)) 0) i i
  | k + 1 => fun i => chain (parentOf A (fun j i => (ancC A k i).contains j) (k + 1)) i i

def candC (A : Mat) : ℕ → ℕ → ℕ → Bool
  | 0 => fun j i => decide (j < i)
  | k + 1 => fun j i => (ancC A k i).contains j

def parentC (A : Mat) (k i : ℕ) : Option ℕ := parentOf A (candC A k) k i

/-- Definition 5.1. -/
def expandC (A : Mat) (N : ℕ) : Mat :=
  match A with
  | [] => []
  | _ =>
    let r := (A.headD []).length
    let c := A.length - 1
    let rows := (List.range r).filter (fun k => (parentC A k c).isSome)
    match rows.getLast? with
    | none => A.dropLast
    | some m =>
      let p := (parentC A m c).getD 0
      let s := c - p
      let Δ := fun k => colv A c k - colv A p k
      let asc := fun k j => decide (k < m) && (decide (j = 0) || (ancC A k (p + j)).contains p)
      let B := fun q => (List.range s).map fun j =>
        (List.range r).map fun k =>
          if asc k j then colv A (p + j) k + q * Δ k else colv A (p + j) k
      A.take p ++ (List.range (N + 1)).flatMap B

/-! ### Printing / parsing in yaBMS syntax -/

def showMat (A : Mat) : String :=
  String.join (A.map fun c => "(" ++ ",".intercalate (c.map toString) ++ ")")

def parseMat (s : String) : Mat :=
  (s.splitOn ")").filterMap fun t =>
    let t := t.replace "(" ""
    if t.isEmpty then none
    else some ((t.splitOn ",").map fun x => x.trimAscii.toString.toNat!)

def run (s : String) (N : ℕ) : String := showMat (expandC (parseMat s) N)

end BM4C
