/-
  Part III: block formulas (explicit quantifier-block structure), their duals, relativization
  to a set, and elementarity with respect to a finite family of block formulas together with the
  finite-family Tarski–Vaught criterion (the form of Theorem 14.4 used in this development).
-/
import Bm4.SetTheory.Defin
import Bm4.SetTheory.Elem

universe u

namespace BM4.ST

open Fm

/-- Block formulas: a signed Δ₀ matrix (`delta true φ` is `φ`, `delta false φ` is `¬φ`), or a
quantifier block in front of a block formula. -/
inductive BF : Type
  | delta (sign : Bool) (φ : Fm)
  | exs (l : List ℕ) (ψ : BF)
  | alls (l : List ℕ) (ψ : BF)
  deriving DecidableEq

namespace BF

def toFm : BF → Fm
  | delta true φ => φ
  | delta false φ => Fm.not φ
  | exs l ψ => Fm.exs l ψ.toFm
  | alls l ψ => Fm.alls l ψ.toFm

/-- The dual: negation pushed through the blocks (an involution). -/
def dual : BF → BF
  | delta b φ => delta (!b) φ
  | exs l ψ => alls l ψ.dual
  | alls l ψ => exs l ψ.dual

theorem sat_dual (b : BF) : ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}),
    Sat D v b.dual.toFm ↔ ¬ Sat D v b.toFm := by
  induction b with
  | delta sg φ => intro D v; cases sg <;> simp [dual, toFm]
  | exs l ψ ih =>
    intro D v
    simp only [dual, toFm]
    rw [not_sat_exs]
    exact sat_alls_congr (ih D) l v
  | alls l ψ ih =>
    intro D v
    simp only [dual, toFm]
    rw [not_sat_alls]
    exact sat_exs_congr (ih D) l v

theorem fv_dual_toFm (b : BF) : fv b.dual.toFm = fv b.toFm := by
  induction b with
  | delta sg φ => cases sg <;> simp [dual, toFm]
  | exs l ψ ih => simp [dual, toFm, fv_exs, fv_alls, ih]
  | alls l ψ ih => simp [dual, toFm, fv_exs, fv_alls, ih]

@[simp] theorem dual_dual (b : BF) : b.dual.dual = b := by
  induction b with
  | delta sg φ => simp [dual]
  | exs l ψ ih => simp [dual, ih]
  | alls l ψ ih => simp [dual, ih]

/-- Well-formed block formulas: Δ₀ matrices and nonempty blocks. -/
inductive WF : BF → Prop
  | delta {sg : Bool} {φ : Fm} : IsDelta0 φ → WF (delta sg φ)
  | exs {l : List ℕ} (hl : l ≠ []) {ψ : BF} : WF ψ → WF (exs l ψ)
  | alls {l : List ℕ} (hl : l ≠ []) {ψ : BF} : WF ψ → WF (alls l ψ)

theorem WF.dual {b : BF} (h : WF b) : WF b.dual := by
  induction h with
  | delta hφ => exact WF.delta hφ
  | exs hl _ ih => exact WF.alls hl ih
  | alls hl _ ih => exact WF.exs hl ih

/- Strictly alternating block formulas of Σ̂q / Π̂q *shape*: `Sig`/`Pi` record the block structure
alone — the nonempty, strictly alternating quantifier blocks in front of a Δ₀ matrix.  Definition
12.1 of the paper asks in addition that every block consist of pairwise distinct variables; that
is `NodupBlocks` below, so the paper's Σ̂q class of block formulas is the pair
`Sig q b ∧ b.NodupBlocks`.  That pair is what the arithmetized code recognizer `IsSigCodeWD` of
`BFCodeD.lean` recognizes (`isSigCodeWD_iff`) and what `GoodAsnQ` requires; accordingly
`Sig.isSigma` takes `NodupBlocks` as a hypothesis. -/
mutual
inductive Sig : ℕ → BF → Prop
  | zero {sg : Bool} {φ : Fm} : IsDelta0 φ → Sig 0 (delta sg φ)
  | succ {q : ℕ} {l : List ℕ} (hl : l ≠ []) {ψ : BF} : Pi q ψ → Sig (q + 1) (exs l ψ)
inductive Pi : ℕ → BF → Prop
  | zero {sg : Bool} {φ : Fm} : IsDelta0 φ → Pi 0 (delta sg φ)
  | succ {q : ℕ} {l : List ℕ} (hl : l ≠ []) {ψ : BF} : Sig q ψ → Pi (q + 1) (alls l ψ)
end

/-- Definition 12.1: every quantifier block consists of pairwise distinct variables. -/
def NodupBlocks : BF → Prop
  | delta _ _ => True
  | exs l ψ => l.Nodup ∧ NodupBlocks ψ
  | alls l ψ => l.Nodup ∧ NodupBlocks ψ

@[simp] theorem nodupBlocks_delta (sg : Bool) (φ : Fm) : (delta sg φ).NodupBlocks := trivial

@[simp] theorem nodupBlocks_exs (l : List ℕ) (ψ : BF) :
    (exs l ψ).NodupBlocks ↔ l.Nodup ∧ ψ.NodupBlocks := Iff.rfl

@[simp] theorem nodupBlocks_alls (l : List ℕ) (ψ : BF) :
    (alls l ψ).NodupBlocks ↔ l.Nodup ∧ ψ.NodupBlocks := Iff.rfl

theorem toFm_delta_delta0 {sg : Bool} {φ : Fm} (h : IsDelta0 φ) : IsDelta0 (delta sg φ).toFm := by
  cases sg
  · exact h.not
  · exact h

mutual
/-- Definition 12.1: a `Sig q` block formula whose blocks are duplicate-free is a Σ̂q formula.
The `NodupBlocks` hypothesis is exactly the paper's "each block consists of pairwise distinct
variables"; `Sig`/`Pi` alone only record the block *shape*. -/
theorem Sig.isSigma : ∀ {q : ℕ} {b : BF}, Sig q b → NodupBlocks b → IsSigma q b.toFm
  | _, _, .zero h, _ => .zero (toFm_delta_delta0 h)
  | _, _, .succ hl h, hnd => .succ _ hl hnd.1 (Pi.isPi h hnd.2)
theorem Pi.isPi : ∀ {q : ℕ} {b : BF}, Pi q b → NodupBlocks b → IsPi q b.toFm
  | _, _, .zero h, _ => .zero (toFm_delta_delta0 h)
  | _, _, .succ hl h, hnd => .succ _ hl hnd.1 (Sig.isSigma h hnd.2)
end

mutual
theorem Sig.dual : ∀ {q : ℕ} {b : BF}, Sig q b → Pi q b.dual
  | _, _, .zero h => .zero h
  | _, _, .succ hl h => .succ hl (Pi.dual h)
theorem Pi.dual : ∀ {q : ℕ} {b : BF}, Pi q b → Sig q b.dual
  | _, _, .zero h => .zero h
  | _, _, .succ hl h => .succ hl (Sig.dual h)
end

mutual
theorem Sig.wf : ∀ {q : ℕ} {b : BF}, Sig q b → WF b
  | _, _, .zero h => .delta h
  | _, _, .succ hl h => .exs hl (Pi.wf h)
theorem Pi.wf : ∀ {q : ℕ} {b : BF}, Pi q b → WF b
  | _, _, .zero h => .delta h
  | _, _, .succ hl h => .alls hl (Sig.wf h)
end

/-- All sub-block-formulas (including itself). -/
def subs : BF → List BF
  | delta sg φ => [delta sg φ]
  | exs l ψ => exs l ψ :: subs ψ
  | alls l ψ => alls l ψ :: subs ψ

theorem self_mem_subs (b : BF) : b ∈ b.subs := by
  cases b <;> simp [subs]

theorem subs_exs_mem {l : List ℕ} {ψ : BF} : ψ ∈ (exs l ψ).subs := by
  simp [subs, self_mem_subs]

theorem subs_alls_mem {l : List ℕ} {ψ : BF} : ψ ∈ (alls l ψ).subs := by
  simp [subs, self_mem_subs]

theorem subs_trans {a b c : BF} (hab : a ∈ b.subs) (hbc : b ∈ c.subs) : a ∈ c.subs := by
  induction c with
  | delta sg φ => simp [subs] at hbc; subst hbc; simpa [subs] using hab
  | exs l ψ ih =>
    simp only [subs, List.mem_cons] at hbc ⊢
    rcases hbc with rfl | hbc
    · simpa [subs] using hab
    · exact Or.inr (ih hbc)
  | alls l ψ ih =>
    simp only [subs, List.mem_cons] at hbc ⊢
    rcases hbc with rfl | hbc
    · simpa [subs] using hab
    · exact Or.inr (ih hbc)

/-- A family closed under sub-formulas and duals. -/
def Closed (F : List BF) : Prop :=
  (∀ b ∈ F, ∀ c ∈ b.subs, c ∈ F) ∧ (∀ b ∈ F, b.dual ∈ F)

/-- The closure of a list of block formulas under sub-formulas and duals. -/
def closure (F : List BF) : List BF :=
  (F.flatMap subs) ++ (F.flatMap subs).map dual

theorem subs_dual (b : BF) : b.dual.subs = b.subs.map dual := by
  induction b with
  | delta sg φ => rfl
  | exs l ψ ih => simp [subs, dual, ih]
  | alls l ψ ih => simp [subs, dual, ih]

theorem closure_closed (F : List BF) : Closed (closure F) := by
  constructor
  · intro b hb c hc
    simp only [closure, List.mem_append, List.mem_flatMap, List.mem_map] at hb ⊢
    rcases hb with ⟨a, ha, hba⟩ | ⟨b', ⟨a, ha, hb'a⟩, rfl⟩
    · exact Or.inl ⟨a, ha, subs_trans hc hba⟩
    · rw [subs_dual, List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      exact Or.inr ⟨c', ⟨a, ha, subs_trans hc' hb'a⟩, rfl⟩
  · intro b hb
    simp only [closure, List.mem_append, List.mem_flatMap, List.mem_map] at hb ⊢
    rcases hb with ⟨a, ha, hba⟩ | ⟨b', hb', rfl⟩
    · exact Or.inr ⟨b, ⟨a, ha, hba⟩, rfl⟩
    · rw [dual_dual]; exact Or.inl hb'

theorem subset_closure (F : List BF) : ∀ b ∈ F, b ∈ closure F := by
  intro b hb
  simp only [closure, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨b, hb, self_mem_subs b⟩

theorem closure_mono {F G : List BF} (h : ∀ b ∈ F, b ∈ G) : ∀ b ∈ closure F, b ∈ closure G := by
  intro b hb
  simp only [closure, List.mem_append, List.mem_flatMap, List.mem_map] at hb ⊢
  rcases hb with ⟨a, ha, hba⟩ | ⟨b', ⟨a, ha, hb'a⟩, rfl⟩
  · exact Or.inl ⟨a, h a ha, hba⟩
  · exact Or.inr ⟨b', ⟨a, h a ha, hb'a⟩, rfl⟩

/-! ### Elementarity for a finite family -/

/-- `M ≺_F N`: all block formulas of `F` with parameters in `M` have the same truth value in `M`
and `N`. -/
def ElemF (F : List BF) (M N : ZFSet.{u}) : Prop :=
  M ⊆ N ∧ ∀ b ∈ F, ∀ v : ℕ → ZFSet.{u}, (∀ x ∈ fv b.toFm, v x ∈ M) →
    (SatIn M v b.toFm ↔ SatIn N v b.toFm)

theorem ElemF.subset {F : List BF} {M N : ZFSet.{u}} (h : ElemF F M N) : M ⊆ N := h.1

theorem ElemF.refl (F : List BF) (M : ZFSet.{u}) : ElemF F M M :=
  ⟨subset_rfl, fun _ _ _ _ => Iff.rfl⟩

theorem ElemF.trans {F : List BF} {M N P : ZFSet.{u}} (h₁ : ElemF F M N) (h₂ : ElemF F N P) :
    ElemF F M P :=
  ⟨h₁.1.trans h₂.1, fun b hb v hv =>
    (h₁.2 b hb v hv).trans (h₂.2 b hb v (fun x hx => h₁.1 (hv x hx)))⟩

theorem ElemF.mono {F G : List BF} (hFG : ∀ b ∈ F, b ∈ G) {M N : ZFSet.{u}} (h : ElemF G M N) :
    ElemF F M N :=
  ⟨h.1, fun b hb => h.2 b (hFG b hb)⟩

/-- Full elementarity (all Σ̂/Π̂ formulas) implies elementarity for every family of well-formed
block formulas of bounded complexity. -/
theorem ElemF.of_elemHat {F : List BF} {q : ℕ} (hF : ∀ b ∈ F, Sig q b ∨ Pi q b)
    (hnd : ∀ b ∈ F, NodupBlocks b) {M N : ZFSet.{u}}
    (h : ElemHat q M N) : ElemF F M N := by
  refine ⟨h.subset, fun b hb v hv => ?_⟩
  rcases hF b hb with hb' | hb'
  · exact h.sigma le_rfl (hb'.isSigma (hnd b hb)) hv
  · exact h.pi le_rfl (hb'.isPi (hnd b hb)) hv

/-- The block formulas of a family which start with an existential block. -/
def IsExs : BF → Prop
  | exs _ _ => True
  | _ => False

instance : DecidablePred IsExs := fun b => by cases b <;> simp [IsExs] <;> infer_instance

/-- **Finite-family Tarski–Vaught**: if `F` is closed under sub-formulas and duals, all its members
are well-formed, `M ⊆ N` are transitive, and every existential member of `F` true in `N` (with
parameters in `M`) is true in `M`, then `M ≺_F N`. -/
theorem elemF_of_downward {F : List BF} (hF : Closed F) (hwf : ∀ b ∈ F, WF b) {M N : ZFSet.{u}}
    (hM : M.IsTransitive) (hN : N.IsTransitive) (hMN : M ⊆ N)
    (hdown : ∀ b ∈ F, IsExs b → ∀ v, (∀ x ∈ fv b.toFm, v x ∈ M) →
      SatIn N v b.toFm → SatIn M v b.toFm) : ElemF F M N := by
  refine ⟨hMN, ?_⟩
  intro b
  induction b with
  | delta sg φ =>
    intro hb v hv
    have hφ : IsDelta0 (delta sg φ).toFm := by
      have := hwf _ hb
      cases this with
      | delta h => exact toFm_delta_delta0 h
    exact hφ.satIn_iff_satIn hM hN hMN hv
  | exs l ψ ih =>
    intro hb v hv
    have hψ : ψ ∈ F := hF.1 _ hb _ subs_exs_mem
    constructor
    · exact sat_exs_mono hMN l (fun w hw h => (ih hψ w hw).mp h) v hv
    · exact hdown _ hb trivial v hv
  | alls l ψ ih =>
    intro hb v hv
    have hψ : ψ ∈ F := hF.1 _ hb _ subs_alls_mem
    have hd : (alls l ψ).dual ∈ F := hF.2 _ hb
    constructor
    · intro hM'
      by_contra hN'
      have h1 : SatIn N v (alls l ψ).dual.toFm := (sat_dual _ _ v).mpr hN'
      have hfv : ∀ x ∈ fv (alls l ψ).dual.toFm, v x ∈ M := by
        intro x hx
        rw [fv_dual_toFm] at hx
        exact hv x hx
      have h2 : SatIn M v (alls l ψ).dual.toFm := hdown _ hd trivial v hfv h1
      exact (sat_dual _ _ v).mp h2 hM'
    · exact sat_alls_anti hMN l (fun w hw h => (ih hψ w hw).mpr h) v hv

end BF

end BM4.ST
