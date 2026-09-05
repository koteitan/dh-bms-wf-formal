/-
  BM4 (Bashicu Matrix System ver. 4): arrays, parents, ancestors, one-step expansion.
  Follows Part I–II of the paper (Definitions 1.1, 2.1, 5.1).
-/
import Mathlib

open Classical

namespace BM4

/-- An `r`-row array of length `len`. Column `i` is `col i : ℕ → ℕ` (row `k ↦` entry).
Only rows `k < r` and positions `i < len` are meaningful; the parent/ancestor relations below
never look at `len`, which makes prefix invariance (Lemma 3.1) automatic. -/
structure Arr (r : ℕ) where
  len : ℕ
  col : ℕ → ℕ → ℕ

variable {r : ℕ}

/-- `parentRel A cand k j i`: `j` is the `k`-parent of `i`, given the structural
candidate relation `cand` for row `k`: `j` is a valid structural candidate and every
larger structural candidate is invalid. -/
def parentRel (A : Arr r) (cand : ℕ → ℕ → Prop) (k : ℕ) (j i : ℕ) : Prop :=
  j < i ∧ cand j i ∧ A.col j k < A.col i k ∧
    ∀ j', j < j' → j' < i → cand j' i → A.col i k ≤ A.col j' k

/-- Strict `k`-ancestor relation `j ≺ᴬₖ i`, by recursion on the row `k`.
Structural `0`-candidates are all `j < i`; structural `(k+1)`-candidates are strict `k`-ancestors. -/
def anc (A : Arr r) : ℕ → ℕ → ℕ → Prop
  | 0 => Relation.TransGen (parentRel A (fun j i => j < i) 0)
  | k + 1 => Relation.TransGen (parentRel A (anc A k) (k + 1))

/-- Structural `k`-candidates. -/
def cand (A : Arr r) : ℕ → ℕ → ℕ → Prop
  | 0 => fun j i => j < i
  | k + 1 => anc A k

/-- `parent A k j i`: `j` is the `k`-parent of `i`. -/
def parent (A : Arr r) (k : ℕ) : ℕ → ℕ → Prop := parentRel A (cand A k) k

/-- Non-strict ancestor `j ≼ᴬₖ i`. -/
def ancEq (A : Arr r) (k j i : ℕ) : Prop := j = i ∨ anc A k j i

/-- `i` has a `k`-parent. -/
def HasParent (A : Arr r) (k i : ℕ) : Prop := ∃ j, parent A k j i

/-! ### Expansion (Definition 5.1) -/

/-- The columns of `G ⌢ B₀ ⌢ B₁ ⌢ ⋯` (infinitely many copies): `p` is the bad root,
`m` the maximal parent row of the last column `c = A.len - 1`, `s = c - p` the length of the
bad part. Position `p + q*s + j` (with `j < s`) is column `j` of copy `q`. -/
noncomputable def tildeCol (A : Arr r) (p m s : ℕ) : ℕ → ℕ → ℕ := fun i k =>
  if i < p then A.col i k
  else
    let q := (i - p) / s
    let j := (i - p) % s
    if k < m ∧ ancEq A k p (p + j) then A.col (p + j) k + q * (A.col (A.len - 1) k - A.col p k)
    else A.col (p + j) k

/-- The last column has a parent in some row `k < r`. -/
def LastHasParent (A : Arr r) : Prop :=
  0 < A.len ∧ ∃ k < r, HasParent A k (A.len - 1)

/-- Maximal parent row `m₀` of the last column (meaningful only when `LastHasParent A`). -/
noncomputable def m₀ (A : Arr r) : ℕ :=
  Nat.findGreatest (fun k => HasParent A k (A.len - 1)) (r - 1)

/-- Position `p` of the `m₀`-parent of the last column. -/
noncomputable def badRoot (A : Arr r) : ℕ :=
  if h : HasParent A (m₀ A) (A.len - 1) then Classical.choose h else 0

/-- Remove the last column. -/
def dropLast (A : Arr r) : Arr r := ⟨A.len - 1, A.col⟩

/-- `A[N]`, Definition 5.1. -/
noncomputable def expand (A : Arr r) (N : ℕ) : Arr r :=
  if A.len = 0 then A
  else if LastHasParent A then
    let p := badRoot A
    let s := A.len - 1 - p
    ⟨p + (N + 1) * s, tildeCol A p (m₀ A) s⟩
  else dropLast A

/-! ### Standard initial arrays, BM4, and the main statements -/

/-- `E_r = ((0,…,0),(1,…,1))`. -/
def E (r : ℕ) : Arr r := ⟨2, fun i _ => if i = 0 then 0 else 1⟩

/-- Arrays reachable from `E r` by finitely many expansions (this is BM4 with `r` rows). -/
inductive Reachable (r : ℕ) : Arr r → Prop
  | init : Reachable r (E r)
  | step {A : Arr r} (N : ℕ) : Reachable r A → Reachable r (expand A N)

/-- The expansion sequence `A₀ = A`, `A_{t+1} = A_t[n_t]`. -/
noncomputable def seq (A : Arr r) (n : ℕ → ℕ) : ℕ → Arr r
  | 0 => A
  | t + 1 => expand (seq A n t) (n t)

/-- One-step expansion relation on BM4 (Section 22): `A R B` iff `B ≠ ∅` and `A = B[n]`. -/
def R (r : ℕ) (A B : Arr r) : Prop :=
  Reachable r B ∧ 0 < B.len ∧ ∃ n, A = expand B n

end BM4
