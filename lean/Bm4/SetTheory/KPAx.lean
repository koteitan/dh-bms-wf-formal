/-
  Part III, §11: the axioms of Kripke–Platek set theory as explicit formulas of our syntax,
  and the Δ₀ predicate `KPAxCode` recognising their codes (the paper's `KPAx`).

  What is recognised for the three schemas is the **universal closure** of an instance, so that
  every recognised code is the code of a *sentence* (`fv_eq_empty_of_kpAxCode`); that is what
  Definition 11.1 needs, since it asserts truth at the empty assignment only.  The closure is
  recognised by `AllsW` below, and the side conditions "the schema variable does not occur free
  in the instance formula" by `NotFreeW` of `Bm4/SetTheory/CodeFV.lean`.
-/
import Bm4.SetTheory.CodeFV

universe u

namespace BM4.ST

/-! ### Code constructors at the level of sets -/

def cFal : ZFSet.{u} := ZFSet.pair (natZ 0) (natZ 0)
def cEq (a b : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (natZ 1) (ZFSet.pair a b)
def cMem (a b : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (natZ 2) (ZFSet.pair a b)
def cImp (a b : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (natZ 3) (ZFSet.pair a b)
def cAll (a b : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (natZ 4) (ZFSet.pair a b)
def cNot (a : ZFSet.{u}) : ZFSet.{u} := cImp a cFal
def cAnd (a b : ZFSet.{u}) : ZFSet.{u} := cNot (cImp a (cNot b))
def cIff (a b : ZFSet.{u}) : ZFSet.{u} := cAnd (cImp a b) (cImp b a)
def cEx (i a : ZFSet.{u}) : ZFSet.{u} := cNot (cAll i (cNot a))
def cBall (i j a : ZFSet.{u}) : ZFSet.{u} := cAll i (cImp (cMem i j) a)
def cBex (i j a : ZFSet.{u}) : ZFSet.{u} := cNot (cBall i j (cNot a))

theorem code_falsum : Fm.code.{u} Fm.falsum = cFal := rfl
theorem code_eq (i j : ℕ) : Fm.code.{u} (Fm.eq i j) = cEq (natZ i) (natZ j) := rfl
theorem code_mem (i j : ℕ) : Fm.code.{u} (Fm.mem i j) = cMem (natZ i) (natZ j) := rfl
theorem code_imp (φ ψ : Fm) : Fm.code.{u} (Fm.imp φ ψ) = cImp φ.code ψ.code := rfl
theorem code_all (i : ℕ) (φ : Fm) : Fm.code.{u} (Fm.all i φ) = cAll (natZ i) φ.code := rfl
theorem code_not (φ : Fm) : Fm.code.{u} (Fm.not φ) = cNot φ.code := rfl
theorem code_and (φ ψ : Fm) : Fm.code.{u} (Fm.and φ ψ) = cAnd φ.code ψ.code := rfl
theorem code_iff (φ ψ : Fm) : Fm.code.{u} (Fm.iff φ ψ) = cIff φ.code ψ.code := rfl
theorem code_ex (i : ℕ) (φ : Fm) : Fm.code.{u} (Fm.ex i φ) = cEx (natZ i) φ.code := rfl
theorem code_ballC (i j : ℕ) (φ : Fm) :
    Fm.code.{u} (Fm.ball i j φ) = cBall (natZ i) (natZ j) φ.code := rfl
theorem code_bex (i j : ℕ) (φ : Fm) :
    Fm.code.{u} (Fm.bex i j φ) = cBex (natZ i) (natZ j) φ.code := rfl

/-! ### Δ₀-definability of constant hereditarily finite sets -/

/-- `S` is a set for which `v e = S` is Δ₀-definable, uniformly in the variable `e`. -/
def D0C (S : ZFSet.{u}) : Prop := ∀ e : ℕ, Delta0Def.{u} {e} (fun _ v => v e = S)

theorem d0c_natZ (k : ℕ) : D0C (natZ.{u} k) := delta0_isNatZ k

theorem d0c_pair {A B : ZFSet.{u}} (hA : D0C A) (hB : D0C B) : D0C (ZFSet.pair A B) := by
  intro e
  set m := e + 1 with hm
  have body := (hA (m + 1)).and ((hB (m + 3)).and
    (delta0_isKPair e (m + 1) (m + 3) (by omega) (by omega)))
  have h1 := body.bex (m + 3) (m + 2) (by omega)
  have h2 := h1.bex (m + 2) e (by omega)
  have h3 := h2.bex (m + 1) m (by omega)
  have h4 := h3.bex m e (by omega)
  refine (h4.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨q, _, a, _, q', _, b, _, rfl, rfl, H⟩; exact H
    · intro H
      exact ⟨_, by rw [H]; exact singleton_mem_pair _ _, A, ZFSet.mem_singleton.mpr rfl,
        _, by rw [H]; exact upair_mem_pair _ _, B, mem_upair_right _ _, rfl, rfl, H⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem d0c_code (φ : Fm) : D0C (Fm.code.{u} φ) := by
  induction φ with
  | falsum => exact d0c_pair (d0c_natZ 0) (d0c_natZ 0)
  | eq i j => exact d0c_pair (d0c_natZ 1) (d0c_pair (d0c_natZ i) (d0c_natZ j))
  | mem i j => exact d0c_pair (d0c_natZ 2) (d0c_pair (d0c_natZ i) (d0c_natZ j))
  | imp φ ψ ih₁ ih₂ => exact d0c_pair (d0c_natZ 3) (d0c_pair ih₁ ih₂)
  | all i φ ih => exact d0c_pair (d0c_natZ 4) (d0c_pair (d0c_natZ i) ih)

/-! ### Δ₀-definability of code shapes with five holes -/

/-- `S` is a five-place shape for which `v e = S (v m) (v (m+1)) (v (m+2)) (v (m+3)) (v (m+4))`
is Δ₀-definable. -/
def D0Sh (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) : Prop :=
  ∀ e m : ℕ, (e < m ∨ m + 4 < e) →
    Delta0Def.{u} {e, m, m + 1, m + 2, m + 3, m + 4}
      (fun _ v => v e = S (v m) (v (m + 1)) (v (m + 2)) (v (m + 3)) (v (m + 4)))

theorem d0sh_const {S : ZFSet.{u}} (h : D0C S) : D0Sh (fun _ _ _ _ _ => S) := by
  intro e m _
  exact (h e).mono (by intro k hk; simp only [Finset.mem_singleton] at hk; simp [hk])

theorem d0sh_p0 : D0Sh.{u} (fun a _ _ _ _ => a) := by
  intro e m _
  exact (Delta0Def.eq e m).mono (by
    intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto)

theorem d0sh_p1 : D0Sh.{u} (fun _ b _ _ _ => b) := by
  intro e m _
  exact (Delta0Def.eq e (m + 1)).mono (by
    intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto)

theorem d0sh_p2 : D0Sh.{u} (fun _ _ x _ _ => x) := by
  intro e m _
  exact (Delta0Def.eq e (m + 2)).mono (by
    intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto)

theorem d0sh_p3 : D0Sh.{u} (fun _ _ _ y _ => y) := by
  intro e m _
  exact (Delta0Def.eq e (m + 3)).mono (by
    intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto)

theorem d0sh_p4 : D0Sh.{u} (fun _ _ _ _ c => c) := by
  intro e m _
  exact (Delta0Def.eq e (m + 4)).mono (by
    intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto)

theorem d0sh_pair {S₁ S₂ : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) :
    D0Sh (fun a b x y c => ZFSet.pair (S₁ a b x y c) (S₂ a b x y c)) := by
  intro e m hem
  set M := e + m + 5 with hM
  have body := (h₁ (M + 1) m (by omega)).and ((h₂ (M + 3) m (by omega)).and
    (delta0_isKPair e (M + 1) (M + 3) (by omega) (by omega)))
  have h1 := body.bex (M + 3) (M + 2) (by omega)
  have h2 := h1.bex (M + 2) e (by omega)
  have h3 := h2.bex (M + 1) M (by omega)
  have h4 := h3.bex M e (by omega)
  refine (h4.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨q, _, a, _, q', _, b, _, rfl, rfl, H⟩; exact H
    · intro H
      exact ⟨_, by rw [H]; exact singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl,
        _, by rw [H]; exact upair_mem_pair _ _, _, mem_upair_right _ _, rfl, rfl, H⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Δ₀ shapes for the derived code constructors -/

variable {S S₁ S₂ S₃ : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}

theorem d0sh_tag (t : ℕ) (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) :
    D0Sh (fun a b x y c => ZFSet.pair (natZ t) (ZFSet.pair (S₁ a b x y c) (S₂ a b x y c))) :=
  d0sh_pair (d0sh_const (d0c_natZ t)) (d0sh_pair h₁ h₂)

theorem d0sh_cFal : D0Sh.{u} (fun _ _ _ _ _ => cFal) :=
  d0sh_const (d0c_pair (d0c_natZ 0) (d0c_natZ 0))

theorem d0sh_cEq (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) :
    D0Sh (fun a b x y c => cEq (S₁ a b x y c) (S₂ a b x y c)) := d0sh_tag 1 h₁ h₂

theorem d0sh_cMem (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) :
    D0Sh (fun a b x y c => cMem (S₁ a b x y c) (S₂ a b x y c)) := d0sh_tag 2 h₁ h₂

theorem d0sh_cImp (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) :
    D0Sh (fun a b x y c => cImp (S₁ a b x y c) (S₂ a b x y c)) := d0sh_tag 3 h₁ h₂

theorem d0sh_cAll (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) :
    D0Sh (fun a b x y c => cAll (S₁ a b x y c) (S₂ a b x y c)) := d0sh_tag 4 h₁ h₂

theorem d0sh_cNot (h : D0Sh S) : D0Sh (fun a b x y c => cNot (S a b x y c)) :=
  d0sh_cImp h d0sh_cFal

theorem d0sh_cAnd (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) :
    D0Sh (fun a b x y c => cAnd (S₁ a b x y c) (S₂ a b x y c)) :=
  d0sh_cNot (d0sh_cImp h₁ (d0sh_cNot h₂))

theorem d0sh_cIff (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) :
    D0Sh (fun a b x y c => cIff (S₁ a b x y c) (S₂ a b x y c)) :=
  d0sh_cAnd (d0sh_cImp h₁ h₂) (d0sh_cImp h₂ h₁)

theorem d0sh_cEx (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) :
    D0Sh (fun a b x y c => cEx (S₁ a b x y c) (S₂ a b x y c)) :=
  d0sh_cNot (d0sh_cAll h₁ (d0sh_cNot h₂))

theorem d0sh_cBall (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) (h₃ : D0Sh S₃) :
    D0Sh (fun a b x y c => cBall (S₁ a b x y c) (S₂ a b x y c) (S₃ a b x y c)) :=
  d0sh_cAll h₁ (d0sh_cImp (d0sh_cMem h₁ h₂) h₃)

theorem d0sh_cBex (h₁ : D0Sh S₁) (h₂ : D0Sh S₂) (h₃ : D0Sh S₃) :
    D0Sh (fun a b x y c => cBex (S₁ a b x y c) (S₂ a b x y c) (S₃ a b x y c)) :=
  d0sh_cNot (d0sh_cBall h₁ h₂ (d0sh_cNot h₃))

/-! ### Codes with bounded variable indices

`DerSeqBW w n s` is a derivation sequence (as in §8) whose *variable indices* are all elements of
`n`; the length of the sequence is still bounded by `w`.  This decoupling is what lets us state
"all variables of the coded formula lie below `N`" without also bounding the size of the formula.
-/

/-- Derivation sequences with all variable indices in `n` and domain in `w`. -/
def DerSeqBW (w n s : ZFSet.{u}) : Prop :=
  IsFunc s ∧ (∃ d ∈ w, IsDom s d) ∧
  ∀ k e, ZFSet.pair k e ∈ s →
    IsAtomicCodeW n e ∨
    (∃ k₁ ∈ k, ∃ k₂ ∈ k, ∃ e₁ e₂, ZFSet.pair k₁ e₁ ∈ s ∧ ZFSet.pair k₂ e₂ ∈ s ∧
      e = ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂)) ∨
    (∃ k₁ ∈ k, ∃ e₁, ∃ i ∈ n, ZFSet.pair k₁ e₁ ∈ s ∧ e = ZFSet.pair (natZ 4) (ZFSet.pair i e₁))

/-- `e` is the code of a formula all of whose variable indices lie in `n`. -/
def IsCodeBW (h w n e : ZFSet.{u}) : Prop :=
  ∃ s ∈ h, DerSeqBW w n s ∧ ∃ k, ZFSet.pair k e ∈ s

theorem delta0_derSeqBW (w n s : ℕ) (hwn : w ≠ n) (hws : w ≠ s) (hns : n ≠ s) :
    Delta0Def {w, n, s} (fun _ v => DerSeqBW (v w) (v n) (v s)) := by
  set m := w + n + s + 1 with hm
  have h1 := delta0_isFunc s
  have h2 := (delta0_isDom s m (by omega)).bex m w (by omega)
  have i0 := (delta0_isKPair (m + 8) (m + 6) (m + 10) (by omega) (by omega)).and
    ((delta0_isKPair (m + 11) (m + 7) (m + 13) (by omega) (by omega)).and
      (delta0_tagPair 3 (m + 5) (m + 10) (m + 13) (by omega) (by omega)))
  have i1 := i0.bex (m + 13) (m + 12) (by omega)
  have i2 := i1.bex (m + 12) (m + 11) (by omega)
  have i3 := i2.bex (m + 11) s (by omega)
  have i4 := i3.bex (m + 10) (m + 9) (by omega)
  have i5 := i4.bex (m + 9) (m + 8) (by omega)
  have i6 := i5.bex (m + 8) s (by omega)
  have i7 := i6.bex (m + 7) (m + 3) (by omega)
  have iC := i7.bex (m + 6) (m + 3) (by omega)
  have a0 := (delta0_isKPair (m + 8) (m + 6) (m + 10) (by omega) (by omega)).and
    (delta0_tagPair 4 (m + 5) (m + 14) (m + 10) (by omega) (by omega))
  have a1 := a0.bex (m + 14) n (by omega)
  have a2 := a1.bex (m + 10) (m + 9) (by omega)
  have a3 := a2.bex (m + 9) (m + 8) (by omega)
  have a4 := a3.bex (m + 8) s (by omega)
  have aC := a4.bex (m + 6) (m + 3) (by omega)
  have c0 := (delta0_isKPair (m + 1) (m + 3) (m + 5) (by omega) (by omega)).imp
    ((delta0_isAtomicCodeW n (m + 5) (by omega)).or (iC.or aC))
  have c1 := c0.ball (m + 5) (m + 4) (by omega)
  have c2 := c1.ball (m + 4) (m + 1) (by omega)
  have c3 := c2.ball (m + 3) (m + 2) (by omega)
  have c4 := c3.ball (m + 2) (m + 1) (by omega)
  have h3 := c4.ball (m + 1) s (by omega)
  refine ((h1.and (h2.and h3)).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold DerSeqBW
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    rw [forall_pair_mem_iff_bounded]
    apply forall_congr'; intro p; apply imp_congr_right; intro _
    apply forall_congr'; intro q; apply imp_congr_right; intro _
    apply forall_congr'; intro k; apply imp_congr_right; intro _
    apply forall_congr'; intro q'; apply imp_congr_right; intro _
    apply forall_congr'; intro e; apply imp_congr_right; intro _
    apply imp_congr_right; intro _
    apply or_congr Iff.rfl
    apply or_congr
    · apply exists_congr; intro k₁; apply and_congr_right; intro _
      apply exists_congr; intro k₂; apply and_congr_right; intro _
      constructor
      · rintro ⟨p₁, hp₁, q₁, _, e₁, _, p₂, hp₂, q₂, _, e₂, _, rfl, rfl, H⟩
        exact ⟨e₁, e₂, hp₁, hp₂, H⟩
      · rintro ⟨e₁, e₂, hh₁, hh₂, H⟩
        exact ⟨_, hh₁, _, upair_mem_pair _ _, e₁, mem_upair_right _ _, _, hh₂,
          _, upair_mem_pair _ _, e₂, mem_upair_right _ _, rfl, rfl, H⟩
    · apply exists_congr; intro k₁; apply and_congr_right; intro _
      constructor
      · rintro ⟨p₁, hp₁, q₁, _, e₁, _, i, hi, rfl, H⟩
        exact ⟨e₁, i, hi, hp₁, H⟩
      · rintro ⟨e₁, i, hi, hh₁, H⟩
        exact ⟨_, hh₁, _, upair_mem_pair _ _, e₁, mem_upair_right _ _, i, hi, rfl, H⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isCodeBW (h w n e : ℕ) (hhw : h ≠ w) (hhn : h ≠ n) (hhe : h ≠ e)
    (hwn : w ≠ n) (hwe : w ≠ e) (hne : n ≠ e) :
    Delta0Def {h, w, n, e} (fun _ v => IsCodeBW (v h) (v w) (v n) (v e)) := by
  set m := h + w + n + e + 1 with hm
  have k0 := delta0_isKPair (m + 1) (m + 3) e (by omega) (by omega)
  have k1 := k0.bex (m + 3) (m + 2) (by omega)
  have k2 := k1.bex (m + 2) (m + 1) (by omega)
  have k3 := k2.bex (m + 1) m (by omega)
  have d := (delta0_derSeqBW w n m (by omega) (by omega) (by omega)).and k3
  have hh := d.bex m h (by omega)
  refine (hh.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold IsCodeBW
    apply exists_congr; intro s; apply and_congr_right; intro _
    apply and_congr_right; intro _
    constructor
    · rintro ⟨p, hp, q, _, k, _, rfl⟩; exact ⟨k, hp⟩
    · rintro ⟨k, hk⟩
      exact ⟨_, hk, _, singleton_mem_pair _ _, k, ZFSet.mem_singleton.mpr rfl, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Correctness of the bounded-variable code recognizer -/

theorem code_eq_inv {ψ : Fm} {a b : ZFSet.{u}}
    (h : Fm.code.{u} ψ = ZFSet.pair (natZ 1) (ZFSet.pair a b)) :
    ∃ i j : ℕ, ψ = Fm.eq i j ∧ a = natZ i ∧ b = natZ j := by
  cases ψ with
  | falsum => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq i j =>
    simp only [Fm.code, ZFSet.pair_inj] at h
    obtain ⟨-, h1, h2⟩ := h
    exact ⟨i, j, rfl, h1.symm, h2.symm⟩
  | mem i j => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | imp φ χ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | all i φ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))

theorem code_mem_inv {ψ : Fm} {a b : ZFSet.{u}}
    (h : Fm.code.{u} ψ = ZFSet.pair (natZ 2) (ZFSet.pair a b)) :
    ∃ i j : ℕ, ψ = Fm.mem i j ∧ a = natZ i ∧ b = natZ j := by
  cases ψ with
  | falsum => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq i j => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | mem i j =>
    simp only [Fm.code, ZFSet.pair_inj] at h
    obtain ⟨-, h1, h2⟩ := h
    exact ⟨i, j, rfl, h1.symm, h2.symm⟩
  | imp φ χ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | all i φ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))

theorem code_all_inv {ψ : Fm} {a b : ZFSet.{u}}
    (h : Fm.code.{u} ψ = ZFSet.pair (natZ 4) (ZFSet.pair a b)) :
    ∃ (i : ℕ) (χ : Fm), ψ = Fm.all i χ ∧ a = natZ i ∧ b = Fm.code.{u} χ := by
  cases ψ with
  | falsum => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq i j => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | mem i j => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | imp φ χ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | all i χ =>
    simp only [Fm.code, ZFSet.pair_inj] at h
    obtain ⟨-, h1, h2⟩ := h
    exact ⟨i, χ, rfl, h1.symm, h2.symm⟩

/-- Every entry of the derivation list of `φ` is the code of a formula whose variables are
among those of `φ`. -/
theorem mem_der_vars : ∀ (φ : Fm), ∀ x ∈ Fm.der.{u} φ,
    ∃ ψ : Fm, x = ψ.code ∧ Fm.vars ψ ⊆ Fm.vars φ := by
  intro φ
  induction φ with
  | falsum => intro x hx; simp only [Fm.der, List.mem_singleton] at hx; exact ⟨_, hx, subset_rfl⟩
  | eq i j => intro x hx; simp only [Fm.der, List.mem_singleton] at hx; exact ⟨_, hx, subset_rfl⟩
  | mem i j => intro x hx; simp only [Fm.der, List.mem_singleton] at hx; exact ⟨_, hx, subset_rfl⟩
  | imp φ ψ ih₁ ih₂ =>
    intro x hx
    simp only [Fm.der, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx | rfl
    · obtain ⟨χ, hχ, hv⟩ := ih₁ x hx
      exact ⟨χ, hχ, hv.trans (by simp only [Fm.vars]; exact Finset.subset_union_left)⟩
    · obtain ⟨χ, hχ, hv⟩ := ih₂ x hx
      exact ⟨χ, hχ, hv.trans (by simp only [Fm.vars]; exact Finset.subset_union_right)⟩
    · exact ⟨_, rfl, subset_rfl⟩
  | all i φ ih =>
    intro x hx
    simp only [Fm.der, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨χ, hχ, hv⟩ := ih x hx
      exact ⟨χ, hχ, hv.trans (by simp only [Fm.vars]; exact Finset.subset_insert _ _)⟩
    · exact ⟨_, rfl, subset_rfl⟩

theorem isAtomicCodeW_bound {N : ℕ} {ψ : Fm} (hv : ∀ k ∈ Fm.vars ψ, k < N)
    (h : IsAtomicCodeW ωZ (Fm.code.{u} ψ)) : IsAtomicCodeW (natZ N) (Fm.code.{u} ψ) := by
  rcases h with h0 | ⟨i, -, j, -, H⟩
  · exact Or.inl h0
  · have key : ∃ i₀ j₀ : ℕ, i = natZ i₀ ∧ j = natZ j₀ ∧ i₀ < N ∧ j₀ < N := by
      rcases H with H | H
      · obtain ⟨i₀, j₀, hψ, ha, hb⟩ := code_eq_inv H
        subst hψ
        exact ⟨i₀, j₀, ha, hb, hv i₀ (by simp [Fm.vars]), hv j₀ (by simp [Fm.vars])⟩
      · obtain ⟨i₀, j₀, hψ, ha, hb⟩ := code_mem_inv H
        subst hψ
        exact ⟨i₀, j₀, ha, hb, hv i₀ (by simp [Fm.vars]), hv j₀ (by simp [Fm.vars])⟩
    obtain ⟨i₀, j₀, rfl, rfl, hi₀, hj₀⟩ := key
    exact Or.inr ⟨_, natZ_mem_natZ_iff.mpr hi₀, _, natZ_mem_natZ_iff.mpr hj₀, H⟩

theorem all_shape_bound {N : ℕ} {ψ : Fm} (hv : ∀ k ∈ Fm.vars ψ, k < N) {i e₁ : ZFSet.{u}}
    (h : Fm.code.{u} ψ = ZFSet.pair (natZ 4) (ZFSet.pair i e₁)) : i ∈ natZ N := by
  obtain ⟨i₀, χ, hψ, ha, -⟩ := code_all_inv h
  subst hψ
  rw [ha]
  exact natZ_mem_natZ_iff.mpr (hv i₀ (by simp [Fm.vars]))

theorem derSeqBW_seqOf_der {N : ℕ} (φ : Fm) (hv : ∀ k ∈ Fm.vars φ, k < N) :
    DerSeqBW ωZ (natZ N) (seqOfAux 0 (Fm.der.{u} φ)) := by
  obtain ⟨hf, hdom, hentry⟩ := derSeqW_seqOf_der.{u} φ
  refine ⟨hf, hdom, ?_⟩
  intro k e hke
  have he : e ∈ Fm.der.{u} φ := by
    obtain ⟨p, x, hx, hpe⟩ := mem_seqOfAux.mp hke
    rw [ZFSet.pair_inj] at hpe
    obtain ⟨-, rfl⟩ := hpe
    obtain ⟨hn, hxx⟩ := List.getElem?_eq_some_iff.mp hx
    exact hxx ▸ List.getElem_mem hn
  obtain ⟨ψ, rfl, hsub⟩ := mem_der_vars φ e he
  have hvψ : ∀ k ∈ Fm.vars ψ, k < N := fun k hk => hv k (hsub hk)
  rcases hentry k _ hke with H | H | ⟨k₁, hk₁, e₁, i, -, h₁, hshape⟩
  · exact Or.inl (isAtomicCodeW_bound hvψ H)
  · exact Or.inr (Or.inl H)
  · exact Or.inr (Or.inr ⟨k₁, hk₁, e₁, i, all_shape_bound hvψ hshape, h₁, hshape⟩)

theorem derSeqBW_entry_isCodeB {N : ℕ} {s : ZFSet.{u}} (hs : DerSeqBW ωZ (natZ N) s) :
    ∀ p e, ZFSet.pair (natZ p) e ∈ s → ∃ φ : Fm, e = Fm.code.{u} φ ∧ ∀ k ∈ Fm.vars φ, k < N := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro e he
  rcases hs.2.2 _ _ he with H | ⟨k₁, hk₁, k₂, hk₂, e₁, e₂, h₁, h₂, rfl⟩ |
    ⟨k₁, hk₁, e₁, i, hi, h₁, rfl⟩
  · rcases H with rfl | ⟨i, hi, j, hj, H⟩
    · exact ⟨.falsum, rfl, by simp [Fm.vars]⟩
    · obtain ⟨i', hi', rfl⟩ := mem_natZ_iff.mp hi
      obtain ⟨j', hj', rfl⟩ := mem_natZ_iff.mp hj
      rcases H with rfl | rfl
      · refine ⟨.eq i' j', rfl, ?_⟩
        intro k hk; simp only [Fm.vars, Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> assumption
      · refine ⟨.mem i' j', rfl, ?_⟩
        intro k hk; simp only [Fm.vars, Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> assumption
  · obtain ⟨p₁, hp₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨p₂, hp₂, rfl⟩ := mem_natZ_iff.mp hk₂
    obtain ⟨φ₁, rfl, hv₁⟩ := ih p₁ hp₁ e₁ h₁
    obtain ⟨φ₂, rfl, hv₂⟩ := ih p₂ hp₂ e₂ h₂
    refine ⟨.imp φ₁ φ₂, rfl, ?_⟩
    intro k hk; simp only [Fm.vars, Finset.mem_union] at hk
    rcases hk with hk | hk
    · exact hv₁ k hk
    · exact hv₂ k hk
  · obtain ⟨p₁, hp₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨φ₁, rfl, hv₁⟩ := ih p₁ hp₁ e₁ h₁
    obtain ⟨i', hi', rfl⟩ := mem_natZ_iff.mp hi
    refine ⟨.all i' φ₁, rfl, ?_⟩
    intro k hk; simp only [Fm.vars, Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact hi'
    · exact hv₁ k hk

/-- Correctness: `IsCodeBW` recognises exactly the codes of formulas with variables below `N`. -/
theorem isCodeBW_iff (N : ℕ) (e : ZFSet.{u}) :
    IsCodeBW (L Ordinal.omega0) ωZ (natZ N) e ↔
      ∃ φ : Fm, e = Fm.code.{u} φ ∧ ∀ k ∈ Fm.vars φ, k < N := by
  constructor
  · rintro ⟨s, -, hs, k, hk⟩
    obtain ⟨d, hd, hdom⟩ := hs.2.1
    have hkd : k ∈ d := (hdom k).mpr ⟨e, hk⟩
    obtain ⟨M, rfl⟩ := mem_ωZ_iff.mp hd
    obtain ⟨p, -, rfl⟩ := mem_natZ_iff.mp hkd
    exact derSeqBW_entry_isCodeB hs p e hk
  · rintro ⟨φ, rfl, hv⟩
    refine ⟨seqOfAux 0 (Fm.der.{u} φ), ?_, derSeqBW_seqOf_der φ hv,
      natZ ((Fm.der.{u} φ).length - 1), ?_⟩
    · apply seqOfAux_mem_Lω
      intro x hx
      obtain ⟨ψ, rfl⟩ := Fm.mem_der.{u} φ x hx
      exact ψ.code_mem_Lω
    · exact mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1, φ.code, Fm.der_last.{u} φ, by simp⟩

/-! ### The axioms of Kripke–Platek set theory

Variables are named by explicit numerals.  In the three schemas the variable names are explicit
parameters; `i` (and, for separation and collection, `j`) are the variables of the instance
formula `φ`, while `x` and `y` are the set variables quantified by the schema. -/

/-- Extensionality: `∀x∀y ((∀u (u ∈ x ↔ u ∈ y)) → x = y)`. -/
def extAx : Fm :=
  Fm.all 0 (Fm.all 1 (Fm.imp (Fm.all 2 (Fm.iff (Fm.mem 2 0) (Fm.mem 2 1))) (Fm.eq 0 1)))

/-- Empty set: `∃x ∀u (u ∉ x)`. -/
def emptyAx : Fm := Fm.ex 0 (Fm.all 1 (Fm.not (Fm.mem 1 0)))

/-- Pairing: `∀x∀y ∃z (x ∈ z ∧ y ∈ z)`. -/
def pairAx : Fm := Fm.all 0 (Fm.all 1 (Fm.ex 2 (Fm.and (Fm.mem 0 2) (Fm.mem 1 2))))

/-- Union: `∀x ∃y ∀u ∈ x, ∀v ∈ u, v ∈ y`. -/
def unionAx : Fm := Fm.all 0 (Fm.ex 1 (Fm.ball 2 0 (Fm.ball 3 2 (Fm.mem 3 1))))

/-- Infinity: there is an inductive set, that is, one containing ∅ and closed under
`u ↦ u ∪ {u}`.  Both `y = ∅` and `v = u ∪ {u}` are rendered by Δ₀ formulas of `{∈}`:
`∃x ((∃y ∈ x, ∀z ∈ y, ⊥) ∧ ∀u ∈ x, ∃v ∈ x (u ∈ v ∧ (∀w ∈ u, w ∈ v) ∧ ∀w ∈ v, (w ∈ u ∨ w = u)))`. -/
def infAx : Fm :=
  Fm.ex 0 (Fm.and
    (Fm.bex 1 0 (Fm.ball 2 1 Fm.falsum))
    (Fm.ball 1 0 (Fm.bex 2 0 (Fm.and (Fm.mem 1 2)
      (Fm.and (Fm.ball 3 1 (Fm.mem 3 2))
        (Fm.ball 3 2 (Fm.or (Fm.mem 3 1) (Fm.eq 3 1))))))))

/-- Δ₀-separation for `φ`: `∀j ∀x ∃y ∀i (i ∈ y ↔ (i ∈ x ∧ φ))`; `j` is the parameter variable. -/
def sepAx (φ : Fm) (i j x y : ℕ) : Fm :=
  Fm.all j (Fm.all x (Fm.ex y (Fm.all i (Fm.iff (Fm.mem i y) (Fm.and (Fm.mem i x) φ)))))

/-- Δ₀-collection for `φ`: `∀x ((∀i ∈ x, ∃j, φ) → ∃y ∀i ∈ x, ∃j ∈ y, φ)`. -/
def collAx (φ : Fm) (i j x y : ℕ) : Fm :=
  Fm.all x (Fm.imp (Fm.ball i x (Fm.ex j φ)) (Fm.ex y (Fm.ball i x (Fm.bex j y φ))))

/-- Set induction (foundation) for `φ` with induction variable `j`:
`(∀j ((∀i ∈ j, φ(i)) → φ)) → ∀j φ`, where `φ(i)` is rendered capture-freely as
`∀j (j = i → φ)`. -/
def indAx (φ : Fm) (i j : ℕ) : Fm :=
  Fm.imp (Fm.all j (Fm.imp (Fm.ball i j (Fm.all j (Fm.imp (Fm.eq j i) φ))) φ)) (Fm.all j φ)

/-! ### The code shapes of the schemas -/

def sepCode (a b x y c : ZFSet.{u}) : ZFSet.{u} :=
  cAll b (cAll x (cEx y (cAll a (cIff (cMem a y) (cAnd (cMem a x) c)))))

def collCode (a b x y c : ZFSet.{u}) : ZFSet.{u} :=
  cAll x (cImp (cBall a x (cEx b c)) (cEx y (cBall a x (cBex b y c))))

def indCode (a b c : ZFSet.{u}) : ZFSet.{u} :=
  cImp (cAll b (cImp (cBall a b (cAll b (cImp (cEq b a) c))) c)) (cAll b c)

theorem sepCode_eq (φ : Fm) (i j x y : ℕ) :
    sepCode (natZ i) (natZ j) (natZ x) (natZ y) (Fm.code.{u} φ) =
      Fm.code.{u} (sepAx φ i j x y) := rfl

theorem collCode_eq (φ : Fm) (i j x y : ℕ) :
    collCode (natZ i) (natZ j) (natZ x) (natZ y) (Fm.code.{u} φ) =
      Fm.code.{u} (collAx φ i j x y) := rfl

theorem indCode_eq (φ : Fm) (i j : ℕ) :
    indCode (natZ i) (natZ j) (Fm.code.{u} φ) = Fm.code.{u} (indAx φ i j) := rfl

theorem d0sh_sepCode : D0Sh.{u} sepCode :=
  d0sh_cAll d0sh_p1 (d0sh_cAll d0sh_p2 (d0sh_cEx d0sh_p3 (d0sh_cAll d0sh_p0
    (d0sh_cIff (d0sh_cMem d0sh_p0 d0sh_p3) (d0sh_cAnd (d0sh_cMem d0sh_p0 d0sh_p2) d0sh_p4)))))

theorem d0sh_collCode : D0Sh.{u} collCode :=
  d0sh_cAll d0sh_p2 (d0sh_cImp (d0sh_cBall d0sh_p0 d0sh_p2 (d0sh_cEx d0sh_p1 d0sh_p4))
    (d0sh_cEx d0sh_p3 (d0sh_cBall d0sh_p0 d0sh_p2 (d0sh_cBex d0sh_p1 d0sh_p3 d0sh_p4))))

theorem d0sh_indCode : D0Sh.{u} (fun a b _ _ c => indCode a b c) :=
  d0sh_cImp (d0sh_cAll d0sh_p1 (d0sh_cImp
      (d0sh_cBall d0sh_p0 d0sh_p1 (d0sh_cAll d0sh_p1 (d0sh_cImp (d0sh_cEq d0sh_p1 d0sh_p0) d0sh_p4)))
      d0sh_p4))
    (d0sh_cAll d0sh_p1 d0sh_p4)

/-! ### Universal closures

`AllsW h w e d` says that `d` is `e` prefixed by a finite (possibly empty) block of universal
quantifiers: `d` codes `Fm.alls l ψ` when `e` codes `ψ`.

No derivation *sequence* is needed here.  It is enough to ask for a set `s ∈ h` that contains `d`
and is closed under "strip one `∀`": every `z ∈ s` is either `e` itself or of the form `∀i z'`
with `z' ∈ s`.  Following that chain downwards from `d` strictly decreases the rank, so it
terminates, and the only place it can stop is `e`. -/
def AllsW (h w e d : ZFSet.{u}) : Prop :=
  ∃ s ∈ h, d ∈ s ∧
    ∀ z ∈ s, z = e ∨ ∃ i ∈ w, ∃ z' ∈ s, z = ZFSet.pair (natZ 4) (ZFSet.pair i z')

-- the distinctness hypotheses are not needed by this proof, but they keep the shape of the other
-- `delta0_*` recognizers of this file
set_option linter.unusedVariables false in
theorem delta0_allsW (h w e d : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwe : w ≠ e) (hwd : w ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, e, d} (fun _ v => AllsW (v h) (v w) (v e) (v d)) := by
  set m := h + w + e + d + 1 with hm
  -- `s := m`, `z := m+1`, `i := m+2`, `z' := m+3`
  have a1 := Delta0Def.eq.{u} (m + 1) e
  have a2 := delta0_tagPair.{u} 4 (m + 1) (m + 2) (m + 3) (by omega) (by omega)
  have a3 := a2.bex (m + 3) m (by omega)
  have a4 := a3.bex (m + 2) w (by omega)
  have a5 := (a1.or a4).ball (m + 1) m (by omega)
  have a6 := (Delta0Def.mem d m).and a5
  have a7 := a6.bex m h (by omega)
  refine ((a7.congr ?_).of_eq ?_)
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- Stripping one `∀` strictly decreases the rank of a code. -/
theorem rank_lt_of_cAll (i z : ZFSet.{u}) : z.rank < (cAll i z).rank :=
  ((ZFSet.rank_lt_of_mem (mem_upair_right i z)).trans
    (ZFSet.rank_lt_of_mem (upair_mem_pair i z))).trans
      ((ZFSet.rank_lt_of_mem (mem_upair_right (natZ 4) (ZFSet.pair i z))).trans
        (ZFSet.rank_lt_of_mem (upair_mem_pair (natZ 4) (ZFSet.pair i z))))

/-- Soundness of `AllsW`: any set closed under "strip one `∀`" over `ψ.code` contains only codes
of universal closures of `ψ`. -/
theorem allsW_entry {s e : ZFSet.{u}}
    (hs : ∀ z ∈ s, z = e ∨ ∃ i ∈ ωZ.{u}, ∃ z' ∈ s, z = ZFSet.pair (natZ 4) (ZFSet.pair i z'))
    {ψ : Fm} (he : e = Fm.code.{u} ψ) :
    ∀ (o : Ordinal.{u}) (z : ZFSet.{u}), z ∈ s → z.rank < o →
      ∃ l : List ℕ, z = Fm.code.{u} (Fm.alls l ψ) := by
  intro o
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    intro z hz hlt
    rcases hs z hz with rfl | ⟨i, hi, z', hz', hzeq⟩
    · exact ⟨[], he⟩
    · obtain ⟨k, rfl⟩ := mem_ωZ_iff.mp hi
      have hrk : z'.rank < z.rank := by
        rw [hzeq]; exact rank_lt_of_cAll _ _
      obtain ⟨l, hl⟩ := ih z.rank hlt z' hz' hrk
      exact ⟨k :: l, by rw [hzeq, hl]; rfl⟩

/-! ### Completeness of `AllsW` -/

/-- The chain of codes `code (alls l ψ)`, `code (alls l.tail ψ)`, …, `code ψ`. -/
def allsChain (ψ : Fm) : List ℕ → List ZFSet.{u}
  | [] => [Fm.code.{u} ψ]
  | i :: l => Fm.code.{u} (Fm.alls (i :: l) ψ) :: allsChain ψ l

theorem head_mem_allsChain (ψ : Fm) : ∀ l : List ℕ,
    Fm.code.{u} (Fm.alls l ψ) ∈ allsChain.{u} ψ l
  | [] => by simp [allsChain]
  | _ :: _ => by simp [allsChain]

theorem allsChain_mem (ψ : Fm) : ∀ (l : List ℕ), ∀ z ∈ allsChain.{u} ψ l,
    ∃ l' : List ℕ, z = Fm.code.{u} (Fm.alls l' ψ) := by
  intro l
  induction l with
  | nil => intro z hz; simp only [allsChain, List.mem_singleton] at hz; exact ⟨[], by simpa using hz⟩
  | cons i l ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨i :: l, rfl⟩
    · exact ih z hz

theorem allsChain_step (ψ : Fm) : ∀ (l : List ℕ), ∀ z ∈ allsChain.{u} ψ l,
    z = Fm.code.{u} ψ ∨ ∃ i : ℕ, ∃ z' ∈ allsChain.{u} ψ l,
      z = ZFSet.pair (natZ 4) (ZFSet.pair (natZ i) z') := by
  intro l
  induction l with
  | nil => intro z hz; simp only [allsChain, List.mem_singleton] at hz; exact Or.inl hz
  | cons i l ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact Or.inr ⟨i, Fm.code.{u} (Fm.alls l ψ),
        List.mem_cons_of_mem _ (head_mem_allsChain ψ l), rfl⟩
    · rcases ih z hz with H | ⟨i', z', hz', H⟩
      · exact Or.inl H
      · exact Or.inr ⟨i', z', List.mem_cons_of_mem _ hz', H⟩

theorem allsW_of_alls (ψ : Fm) (l : List ℕ) :
    AllsW (L Ordinal.omega0) ωZ (Fm.code.{u} ψ) (Fm.code.{u} (Fm.alls l ψ)) := by
  refine ⟨ofList (allsChain.{u} ψ l),
    ofList_mem_L_of_limit Ordinal.isSuccLimit_omega0 _ (fun z hz => ?_),
    mem_ofList.mpr (head_mem_allsChain ψ l), ?_⟩
  · obtain ⟨l', rfl⟩ := allsChain_mem ψ l z hz
    exact Fm.code_mem_Lω _
  · intro z hz
    rcases allsChain_step ψ l z (mem_ofList.mp hz) with H | ⟨i, z', hz', H⟩
    · exact Or.inl H
    · exact Or.inr ⟨natZ i, natZ_mem_ωZ i, z', mem_ofList.mpr hz', H⟩

/-- Correctness: `AllsW` recognises exactly the codes of universal closures of `ψ`. -/
theorem allsW_iff (ψ : Fm) (d : ZFSet.{u}) :
    AllsW (L Ordinal.omega0) ωZ (Fm.code.{u} ψ) d ↔ ∃ l : List ℕ, d = Fm.code.{u} (Fm.alls l ψ) := by
  constructor
  · rintro ⟨s, -, hd, hs⟩
    exact allsW_entry hs rfl (Order.succ d.rank) d hd (Order.lt_succ _)
  · rintro ⟨l, rfl⟩
    exact allsW_of_alls ψ l

/-! ### Bounds on variable indices -/

theorem bound_le_of_lt {φ : Fm} {x : ℕ} (h : ∀ k ∈ Fm.vars φ, k < x) : Fm.bound φ ≤ x := by
  unfold Fm.bound Fm.fresh
  split_ifs with hne
  · have hmem := (Fm.vars φ).max'_mem hne
    have := h _ hmem
    omega
  · omega

theorem lt_bound_vars {φ : Fm} {k : ℕ} (hk : k ∈ Fm.vars φ) : k < Fm.bound φ := Fm.lt_bound hk

/-- A variable index at least as large as every variable index of `φ` does not occur free in `φ`.
This is how the side conditions of the schemas were stated before they were relaxed to the
paper's "does not occur free", and it turns the old hypotheses into the new ones. -/
theorem notFree_of_vars_lt {φ : Fm} {N k : ℕ} (h : ∀ n ∈ Fm.vars φ, n < N) (hk : N ≤ k) :
    k ∉ Fm.fv φ := fun hmem => absurd (h k (Fm.fv_subset_vars φ hmem)) (by omega)

/-- The canonical list of a finite set covers it. -/
theorem subset_toList_toFinset (S : Finset ℕ) : S ⊆ S.toList.toFinset :=
  fun _ hk => List.mem_toFinset.mpr (Finset.mem_toList.mpr hk)

/-! ### The recognizer

`KPAxCode h w d` says that `d` is the code of one of the five closed axioms, or of an instance of
one of the three schemas.  All quantifiers are bounded by `h` (intended `L ω`) and `w` (intended
`ωZ`).

What is recognised for a schema is the **universal closure** of an instance: `d` codes
`Fm.alls l ψ` where `ψ` is the schema instance coded by `q` and the closure is a sentence.  That
is the standard reading of "an instance of an axiom schema", and it is what Definition 11.1 needs:
`KPTrue` may then be asked at the empty assignment only.  The closure is recognised by `AllsW`,
and "the closure is a sentence" by `∀ k ∈ w, NotFreeW h w k d` — a *bounded* quantifier over `w`
(intended `ωZ`), hence Δ₀.

The side conditions on the instance are the paper's: the schema variables must be pairwise
distinct, and they must not occur **free** in the instance formula `c`.  That last condition is
decided by the Δ₀ recognizer `NotFreeW` of `Bm4.SetTheory.CodeFV`.

Which variables have to be non-free:

* separation `∀j ∀x ∃y ∀i (i ∈ y ↔ i ∈ x ∧ φ)` and collection
  `∀x ((∀i ∈ x, ∃j φ) → ∃y ∀i ∈ x, ∃j ∈ y, φ)`: the *witness* variable `y` must not occur free in
  `φ`, otherwise the instance is outright false — for `φ := ¬(j ∈ y)` the antecedent of collection
  reads "for every `i ∈ x` there is a `j` outside the parameter `y`", which is true, while the
  consequent asks for a set `y` with an element `j ∈ y` and `j ∉ y`.  The element variables `i`
  (and `j` for collection) are *supposed* to occur free in `φ`, and a free occurrence of the
  universally quantified `x` is harmless (it is just a parameter); the paper nevertheless states
  the condition for `x` as well, and it is kept here.
* set induction `(∀j ((∀i ∈ j, φ(i)) → φ)) → ∀j φ`, where `φ(i)` is rendered capture-freely as
  `∀j (j = i → φ)`: the auxiliary variable `i` must not occur free in `φ`, or that rendering is
  not a substitution.  The induction variable `j` is the one `φ` is about. -/
def KPAxCode (h w d : ZFSet.{u}) : Prop :=
  d = Fm.code.{u} extAx ∨ d = Fm.code.{u} emptyAx ∨ d = Fm.code.{u} pairAx ∨
  d = Fm.code.{u} unionAx ∨ d = Fm.code.{u} infAx ∨
  ∃ a ∈ w, ∃ b ∈ w, ∃ x ∈ w, ∃ y ∈ w, ∃ c ∈ h, ∃ q ∈ h,
    (∀ k ∈ w, NotFreeW h w k d) ∧ AllsW h w q d ∧
    ((IsDelta0CodeW h w c ∧ NotFreeW h w y c ∧
        a ≠ b ∧ a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y ∧ x ≠ y ∧
        (q = sepCode a b x y c ∨ q = collCode a b x y c)) ∨
      (NotFreeW h w a c ∧ a ≠ b ∧ q = indCode a b c))

theorem delta0_kpAxCode (h w d : ℕ) (hhw : h ≠ w) (hhd : h ≠ d) (hwd : w ≠ d) :
    Delta0Def.{u} {h, w, d} (fun _ v => KPAxCode (v h) (v w) (v d)) := by
  set m := h + w + d + 1 with hm
  -- holes: `a := m`, `b := m+1`, `x := m+2`, `y := m+3`, `c := m+4`, `q := m+5`, `k := m+6`
  have e1 := d0c_code.{u} extAx d
  have e2 := d0c_code.{u} emptyAx d
  have e3 := d0c_code.{u} pairAx d
  have e4 := d0c_code.{u} unionAx d
  have e5 := d0c_code.{u} infAx d
  have C1 := (delta0_notFreeW h w (m + 6) d (by omega) (by omega) hhd (by omega) hwd
    (by omega)).ball (m + 6) w (by omega)
  have C2 := delta0_allsW h w (m + 5) d (by omega) (by omega) hhd (by omega) hwd (by omega)
  have A2 := delta0_isDelta0CodeW h w (m + 4) (by omega) (by omega) (by omega)
  have A4 := delta0_notFreeW h w (m + 3) (m + 4) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have A5 := (Delta0Def.eq m (m + 1)).not
  have A6 := (Delta0Def.eq m (m + 2)).not
  have A7 := (Delta0Def.eq m (m + 3)).not
  have A8 := (Delta0Def.eq (m + 1) (m + 2)).not
  have A9 := (Delta0Def.eq (m + 1) (m + 3)).not
  have A10 := (Delta0Def.eq (m + 2) (m + 3)).not
  have A11 := (d0sh_sepCode (m + 5) m (by omega)).or (d0sh_collCode (m + 5) m (by omega))
  have br1 := A2.and (A4.and (A5.and (A6.and (A7.and (A8.and (A9.and (A10.and A11)))))))
  have B1 := delta0_notFreeW h w m (m + 4) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have br2 := B1.and (A5.and (d0sh_indCode (m + 5) m (by omega)))
  have body := C1.and (C2.and (br1.or br2))
  have q1 := body.bex (m + 5) h (by omega)
  have q2 := q1.bex (m + 4) h (by omega)
  have q3 := q2.bex (m + 3) w (by omega)
  have q4 := q3.bex (m + 2) w (by omega)
  have q5 := q4.bex (m + 1) w (by omega)
  have q6 := q5.bex m w (by omega)
  refine (((e1.or (e2.or (e3.or (e4.or (e5.or q6))))).congr ?_).of_eq ?_)
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Sentences -/

/-- `∀ k ∈ ωZ, NotFreeW … k (code χ)` says exactly that `χ` is a sentence. -/
theorem closedW_of_fv_empty {χ : Fm} (h : Fm.fv χ = ∅) :
    ∀ k ∈ ωZ.{u}, NotFreeW (L Ordinal.omega0) ωZ k (Fm.code.{u} χ) := by
  intro k hk
  obtain ⟨n, rfl⟩ := mem_ωZ_iff.mp hk
  exact (notFreeW_iff n _).mpr ⟨χ, rfl, by rw [h]; exact Finset.notMem_empty n⟩

theorem fv_empty_of_closedW {χ : Fm}
    (h : ∀ k ∈ ωZ.{u}, NotFreeW (L Ordinal.omega0) ωZ k (Fm.code.{u} χ)) : Fm.fv χ = ∅ := by
  by_contra hne
  obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨χ', hχ', hnfv⟩ := (notFreeW_iff n _).mp (h (natZ n) (natZ_mem_ωZ n))
  rw [Fm.code_injective hχ'] at hn
  exact hnfv hn

/-! ### Completeness of the recognizer -/

theorem kpAxCode_ext : KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} extAx) := Or.inl rfl

theorem kpAxCode_empty : KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} emptyAx) :=
  Or.inr (Or.inl rfl)

theorem kpAxCode_pair : KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} pairAx) :=
  Or.inr (Or.inr (Or.inl rfl))

theorem kpAxCode_union : KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} unionAx) :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem kpAxCode_inf : KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} infAx) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- The common part of the two Δ₀ schema instances: the universal closure `alls l ψ` of an
instance `ψ`, closed because `l` covers `Fm.fv ψ`. -/
theorem kpAxCode_schema {φ : Fm} (hφ : Fm.IsDelta0 φ) {i j x y : ℕ} (hy : y ∉ Fm.fv φ)
    (hij : i ≠ j) (hix : i ≠ x) (hiy : i ≠ y) (hjx : j ≠ x) (hjy : j ≠ y) (hxy : x ≠ y)
    {ψ : Fm} (hψ : ψ = sepAx φ i j x y ∨ ψ = collAx φ i j x y)
    (l : List ℕ) (hl : Fm.fv ψ ⊆ l.toFinset) :
    KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} (Fm.alls l ψ)) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨natZ i, natZ_mem_ωZ _, natZ j, natZ_mem_ωZ _, natZ x, natZ_mem_ωZ _,
      natZ y, natZ_mem_ωZ _, Fm.code.{u} φ, φ.code_mem_Lω,
      Fm.code.{u} ψ, ψ.code_mem_Lω, ?_, allsW_of_alls ψ l,
      Or.inl ⟨(isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩, (notFreeW_iff y _).mpr ⟨φ, rfl, hy⟩,
        natZ_ne hij, natZ_ne hix, natZ_ne hiy, natZ_ne hjx, natZ_ne hjy, natZ_ne hxy, ?_⟩⟩))))
  · exact closedW_of_fv_empty
      (by rw [Fm.fv_alls]; exact Finset.sdiff_eq_empty_iff_subset.mpr hl)
  · rcases hψ with rfl | rfl
    · exact Or.inl (sepCode_eq φ i j x y).symm
    · exact Or.inr (collCode_eq φ i j x y).symm

theorem kpAxCode_sep {φ : Fm} (hφ : Fm.IsDelta0 φ) {i j x y : ℕ} (hy : y ∉ Fm.fv φ)
    (hij : i ≠ j) (hix : i ≠ x) (hiy : i ≠ y) (hjx : j ≠ x) (hjy : j ≠ y) (hxy : x ≠ y)
    (l : List ℕ) (hl : Fm.fv (sepAx φ i j x y) ⊆ l.toFinset) :
    KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} (Fm.alls l (sepAx φ i j x y))) :=
  kpAxCode_schema hφ hy hij hix hiy hjx hjy hxy (Or.inl rfl) l hl

theorem kpAxCode_coll {φ : Fm} (hφ : Fm.IsDelta0 φ) {i j x y : ℕ} (hy : y ∉ Fm.fv φ)
    (hij : i ≠ j) (hix : i ≠ x) (hiy : i ≠ y) (hjx : j ≠ x) (hjy : j ≠ y) (hxy : x ≠ y)
    (l : List ℕ) (hl : Fm.fv (collAx φ i j x y) ⊆ l.toFinset) :
    KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} (Fm.alls l (collAx φ i j x y))) :=
  kpAxCode_schema hφ hy hij hix hiy hjx hjy hxy (Or.inr rfl) l hl

theorem kpAxCode_ind {φ : Fm} {i j : ℕ} (hi : i ∉ Fm.fv φ) (hij : i ≠ j)
    (l : List ℕ) (hl : Fm.fv (indAx φ i j) ⊆ l.toFinset) :
    KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} (Fm.alls l (indAx φ i j))) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨natZ i, natZ_mem_ωZ _, natZ j, natZ_mem_ωZ _, natZ 0, natZ_mem_ωZ _,
      natZ 0, natZ_mem_ωZ _, Fm.code.{u} φ, φ.code_mem_Lω,
      Fm.code.{u} (indAx φ i j), (indAx φ i j).code_mem_Lω, ?_,
      allsW_of_alls _ l,
      Or.inr ⟨(notFreeW_iff i _).mpr ⟨φ, rfl, hi⟩, natZ_ne hij,
        (indCode_eq φ i j).symm⟩⟩))))
  · exact closedW_of_fv_empty
      (by rw [Fm.fv_alls]; exact Finset.sdiff_eq_empty_iff_subset.mpr hl)

/-! ### Inversion -/

set_option maxRecDepth 8000 in
theorem kpAxCode_iff (d : ZFSet.{u}) :
    KPAxCode (L Ordinal.omega0) ωZ d ↔
      d = Fm.code.{u} extAx ∨ d = Fm.code.{u} emptyAx ∨ d = Fm.code.{u} pairAx ∨
      d = Fm.code.{u} unionAx ∨ d = Fm.code.{u} infAx ∨
      (∃ (φ : Fm) (i j x y : ℕ), Fm.IsDelta0 φ ∧ y ∉ Fm.fv φ ∧
          i ≠ j ∧ i ≠ x ∧ i ≠ y ∧ j ≠ x ∧ j ≠ y ∧ x ≠ y ∧
          ∃ (l : List ℕ) (ψ : Fm), (ψ = sepAx φ i j x y ∨ ψ = collAx φ i j x y) ∧
            Fm.fv ψ ⊆ l.toFinset ∧ d = Fm.code.{u} (Fm.alls l ψ)) ∨
      (∃ (φ : Fm) (i j : ℕ), i ∉ Fm.fv φ ∧ i ≠ j ∧
          ∃ l : List ℕ, Fm.fv (indAx φ i j) ⊆ l.toFinset ∧
            d = Fm.code.{u} (Fm.alls l (indAx φ i j))) := by
  constructor
  · rintro (H | H | H | H | H | ⟨a, ha, b, hb, x, hx, y, hy, c, -, q, -, hcl, halls, HH⟩)
    · exact Or.inl H
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inr (Or.inl H))
    · exact Or.inr (Or.inr (Or.inr (Or.inl H)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl H))))
    -- every code recognised through `AllsW q d` is a closure of the formula coded by `q`
    have key : ∀ ψ : Fm, q = Fm.code.{u} ψ →
        ∃ l : List ℕ, Fm.fv ψ ⊆ l.toFinset ∧ d = Fm.code.{u} (Fm.alls l ψ) := by
      intro ψ hq
      obtain ⟨l, hdl⟩ := (allsW_iff ψ d).mp (hq ▸ halls)
      refine ⟨l, ?_, hdl⟩
      have hemp : Fm.fv (Fm.alls l ψ) = ∅ := fv_empty_of_closedW (by rw [← hdl]; exact hcl)
      rw [Fm.fv_alls] at hemp
      exact Finset.sdiff_eq_empty_iff_subset.mp hemp
    obtain ⟨i, rfl⟩ := mem_ωZ_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_ωZ_iff.mp hb
    obtain ⟨x', rfl⟩ := mem_ωZ_iff.mp hx
    obtain ⟨y', rfl⟩ := mem_ωZ_iff.mp hy
    rcases HH with ⟨hd0, hyn, hab, hax, hay, hbx, hby, hxy, hshape⟩ | ⟨han, hab, hshape⟩
    · obtain ⟨φ, hφ, rfl⟩ := (isDelta0CodeW_iff _).mp hd0
      obtain ⟨ψy, hψy, hyfv⟩ := (notFreeW_iff y' _).mp hyn
      have hyφ : y' ∉ Fm.fv φ := by rw [Fm.code_injective hψy]; exact hyfv
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨φ, i, j, x', y', hφ, hyφ,
          fun e => hab (by rw [e]), fun e => hax (by rw [e]), fun e => hay (by rw [e]),
          fun e => hbx (by rw [e]), fun e => hby (by rw [e]), fun e => hxy (by rw [e]), ?_⟩)))))
      rcases hshape with hshape | hshape
      · obtain ⟨l, hlsub, hdl⟩ := key (sepAx φ i j x' y') (hshape.trans (sepCode_eq φ i j x' y'))
        exact ⟨l, _, Or.inl rfl, hlsub, hdl⟩
      · obtain ⟨l, hlsub, hdl⟩ := key (collAx φ i j x' y') (hshape.trans (collCode_eq φ i j x' y'))
        exact ⟨l, _, Or.inr rfl, hlsub, hdl⟩
    · obtain ⟨φ, rfl, hifv⟩ := (notFreeW_iff i _).mp han
      obtain ⟨l, hlsub, hdl⟩ := key (indAx φ i j) (hshape.trans (indCode_eq φ i j))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨φ, i, j, hifv, fun e => hab (by rw [e]), l, hlsub, hdl⟩)))))
  · rintro (rfl | rfl | rfl | rfl | rfl |
      ⟨φ, i, j, x, y, hφ, hy, hij, hix, hiy, hjx, hjy, hxy, l, ψ, hψ, hlsub, rfl⟩ |
      ⟨φ, i, j, hi, hij, l, hlsub, rfl⟩)
    · exact kpAxCode_ext
    · exact kpAxCode_empty
    · exact kpAxCode_pair
    · exact kpAxCode_union
    · exact kpAxCode_inf
    · exact kpAxCode_schema hφ hy hij hix hiy hjx hjy hxy hψ l hlsub
    · exact kpAxCode_ind hi hij l hlsub

/-- Every code recognised by `KPAxCode` is the code of a **sentence**.  This is what makes
Definition 11.1's `⟨d, ∅⟩ ∈ S` (truth at the empty assignment) the right reading. -/
theorem fv_eq_empty_of_kpAxCode {d : ZFSet.{u}} (hd : KPAxCode (L Ordinal.omega0) ωZ d)
    {φ : Fm} (hcode : d = Fm.code.{u} φ) : Fm.fv φ = ∅ := by
  have hstep : ∀ (l : List ℕ) (ψ : Fm), Fm.fv ψ ⊆ l.toFinset →
      d = Fm.code.{u} (Fm.alls l ψ) → Fm.fv φ = ∅ := by
    intro l ψ hlsub hdl
    rw [Fm.code_injective (hcode.symm.trans hdl), Fm.fv_alls]
    exact Finset.sdiff_eq_empty_iff_subset.mpr hlsub
  rcases (kpAxCode_iff d).mp hd with H | H | H | H | H |
    ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, l, ψ, -, hlsub, hdl⟩ |
    ⟨_, _, _, -, -, l, hlsub, hdl⟩
  · rw [Fm.code_injective (hcode.symm.trans H)]; decide
  · rw [Fm.code_injective (hcode.symm.trans H)]; decide
  · rw [Fm.code_injective (hcode.symm.trans H)]; decide
  · rw [Fm.code_injective (hcode.symm.trans H)]; decide
  · rw [Fm.code_injective (hcode.symm.trans H)]; decide
  · exact hstep l ψ hlsub hdl
  · exact hstep l _ hlsub hdl

/-- Every code recognised by `KPAxCode` is the code of a formula. -/
theorem exists_fm_of_kpAxCode {d : ZFSet.{u}} (hd : KPAxCode (L Ordinal.omega0) ωZ d) :
    ∃ φ : Fm, d = Fm.code.{u} φ := by
  rcases (kpAxCode_iff d).mp hd with H | H | H | H | H |
    ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, l, ψ, -, -, hs⟩ | ⟨φ, i, j, -, -, l, -, hs⟩
  · exact ⟨extAx, H⟩
  · exact ⟨emptyAx, H⟩
  · exact ⟨pairAx, H⟩
  · exact ⟨unionAx, H⟩
  · exact ⟨infAx, H⟩
  · exact ⟨Fm.alls l ψ, hs⟩
  · exact ⟨Fm.alls l (indAx φ i j), hs⟩

end BM4.ST
