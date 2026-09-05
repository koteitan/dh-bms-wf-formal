/-
  Part III: elementarity for the alternating block hierarchy (Definition 14.1) and the
  Tarski–Vaught criterion at finite level (the semantic content of Theorem 14.4).
-/
import Bm4.SetTheory.Fm

universe u

namespace BM4.ST

open Fm

/-- A valuation takes its values (on a finite set of variables) in `M`. -/
def ValIn (M : ZFSet.{u}) (s : Finset ℕ) (v : ℕ → ZFSet.{u}) : Prop := ∀ x ∈ s, v x ∈ M

/-- `M ≺*q N` (Definition 14.1): for transitive `M ⊆ N` and `q ≥ 1`, for all `1 ≤ j ≤ q`, all
Σ̂j and Π̂j formulas and all valuations of their free variables in `M`, satisfaction in `M` and
in `N` agree.  Level `j = 0` is deliberately excluded: for transitive `M ⊆ N` the Δ₀ case is
automatic (`ElemHat.delta0`). -/
def ElemHat (q : ℕ) (M N : ZFSet.{u}) : Prop :=
  1 ≤ q ∧ M.IsTransitive ∧ N.IsTransitive ∧ M ⊆ N ∧
    ∀ j, 1 ≤ j → j ≤ q → ∀ φ : Fm, (IsSigma j φ ∨ IsPi j φ) →
      ∀ v : ℕ → ZFSet.{u}, ValIn M (fv φ) v → (SatIn M v φ ↔ SatIn N v φ)

theorem ElemHat.one_le {q : ℕ} {M N : ZFSet.{u}} (h : ElemHat q M N) : 1 ≤ q := h.1

theorem ElemHat.transM {q : ℕ} {M N : ZFSet.{u}} (h : ElemHat q M N) : M.IsTransitive := h.2.1

theorem ElemHat.transN {q : ℕ} {M N : ZFSet.{u}} (h : ElemHat q M N) : N.IsTransitive := h.2.2.1

theorem ElemHat.subset {q : ℕ} {M N : ZFSet.{u}} (h : ElemHat q M N) : M ⊆ N := h.2.2.2.1

theorem ElemHat.agree {q : ℕ} {M N : ZFSet.{u}} (h : ElemHat q M N) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ q) {φ : Fm} (hφ : IsSigma j φ ∨ IsPi j φ) {v : ℕ → ZFSet.{u}}
    (hv : ValIn M (fv φ) v) : SatIn M v φ ↔ SatIn N v φ := h.2.2.2.2 j hj1 hj φ hφ v hv

/-- The level `j = 0` omitted from Definition 14.1: Δ₀ absoluteness for transitive `M ⊆ N`. -/
theorem ElemHat.delta0 {q : ℕ} {M N : ZFSet.{u}} (h : ElemHat q M N) {φ : Fm} (hφ : IsDelta0 φ)
    {v : ℕ → ZFSet.{u}} (hv : ValIn M (fv φ) v) : SatIn M v φ ↔ SatIn N v φ :=
  hφ.satIn_iff_satIn h.transM h.transN h.subset hv

/-- Agreement on Σ̂j formulas for every `j ≤ q`.  Definition 14.1 only asks for `1 ≤ j`; the
level `j = 0` (Σ̂₀ = Δ₀) comes for free from `ElemHat.delta0`. -/
theorem ElemHat.sigma {q : ℕ} {M N : ZFSet.{u}} (h : ElemHat q M N) {j : ℕ} (hj : j ≤ q) {φ : Fm}
    (hφ : IsSigma j φ) {v : ℕ → ZFSet.{u}} (hv : ValIn M (fv φ) v) :
    SatIn M v φ ↔ SatIn N v φ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · cases hφ with
    | zero h0 => exact h.delta0 h0 hv
  · exact h.agree hj1 hj (Or.inl hφ) hv

/-- Agreement on Π̂j formulas for every `j ≤ q`; `j = 0` again by Δ₀ absoluteness. -/
theorem ElemHat.pi {q : ℕ} {M N : ZFSet.{u}} (h : ElemHat q M N) {j : ℕ} (hj : j ≤ q) {φ : Fm}
    (hφ : IsPi j φ) {v : ℕ → ZFSet.{u}} (hv : ValIn M (fv φ) v) :
    SatIn M v φ ↔ SatIn N v φ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · cases hφ with
    | zero h0 => exact h.delta0 h0 hv
  · exact h.agree hj1 hj (Or.inr hφ) hv

/-- Lemma 15.1 (1): monotonicity in `q`. -/
theorem ElemHat.mono {q q' : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ q') {M N : ZFSet.{u}}
    (h : ElemHat q' M N) : ElemHat q M N :=
  ⟨hq1, h.transM, h.transN, h.subset, fun j hj1 hj => h.2.2.2.2 j hj1 (hj.trans hq)⟩

/-- Lemma 15.1 (2): transitivity. -/
theorem ElemHat.trans {q : ℕ} {M N P : ZFSet.{u}} (h₁ : ElemHat q M N) (h₂ : ElemHat q N P) :
    ElemHat q M P :=
  ⟨h₁.one_le, h₁.transM, h₂.transN, h₁.subset.trans h₂.subset, fun _ hj1 hj _ hφ _ hv =>
    (h₁.agree hj1 hj hφ hv).trans
      (h₂.agree hj1 hj hφ (fun x hx => h₁.subset (hv x hx)))⟩

theorem ElemHat.refl {q : ℕ} (hq : 1 ≤ q) {M : ZFSet.{u}} (hM : M.IsTransitive) :
    ElemHat q M M := ⟨hq, hM, hM, subset_rfl, fun _ _ _ _ _ _ _ => Iff.rfl⟩

/-- Satisfaction of an existential block over `M` implies it over `N ⊇ M` when the matrix is
absolute upward. -/
theorem sat_exs_mono {M N : ZFSet.{u}} (hMN : M ⊆ N) {χ : Fm} (l : List ℕ)
    (hχ : ∀ v, ValIn M (fv χ) v → SatIn M v χ → SatIn N v χ) :
    ∀ v, ValIn M (fv (exs l χ)) v → SatIn M v (exs l χ) → SatIn N v (exs l χ) := by
  induction l with
  | nil => exact hχ
  | cons i l ih =>
    intro v hv h
    simp only [exs_cons, SatIn, sat_ex] at h ⊢
    obtain ⟨x, hx, h⟩ := h
    refine ⟨x, hMN hx, ih _ ?_ h⟩
    intro y hy
    by_cases hyi : y = i
    · subst hyi; simpa
    · rw [Function.update_of_ne hyi]
      apply hv
      rw [fv_exs] at hy ⊢
      simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons] at hy ⊢
      exact ⟨hy.1, fun h => hy.2 (h.resolve_left hyi)⟩

/-- Dual of `sat_exs_mono`: satisfaction of a universal block over `N ⊇ M` implies it over `M`
when the matrix is absolute downward.  Theorem 14.4 does not need it — there the Π̂ case is
obtained from the Σ̂ case by dualization, as in the paper — but `BF.lean` uses it directly. -/
theorem sat_alls_anti {M N : ZFSet.{u}} (hMN : M ⊆ N) {χ : Fm} (l : List ℕ)
    (hχ : ∀ v, ValIn M (fv χ) v → SatIn N v χ → SatIn M v χ) :
    ∀ v, ValIn M (fv (alls l χ)) v → SatIn N v (alls l χ) → SatIn M v (alls l χ) := by
  induction l with
  | nil => exact hχ
  | cons i l ih =>
    intro v hv h
    simp only [alls_cons, SatIn, sat_all] at h ⊢
    intro x hx
    refine ih _ ?_ (h x (hMN hx))
    intro y hy
    by_cases hyi : y = i
    · subst hyi; simpa
    · rw [Function.update_of_ne hyi]
      apply hv
      rw [fv_alls] at hy ⊢
      simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons] at hy ⊢
      exact ⟨hy.1, fun h => hy.2 (h.resolve_left hyi)⟩

/-- **Tarski–Vaught at finite level** (Theorem 14.4, semantic form). If `q ≥ 1`, `M ⊆ N` are
transitive and every Σ̂j formula (`1 ≤ j ≤ q`) with parameters in `M` true in `N` is true in `M`,
then `M ≺*q N`. -/
theorem elemHat_of_downward {q : ℕ} (hq : 1 ≤ q) {M N : ZFSet.{u}} (hM : M.IsTransitive)
    (hN : N.IsTransitive) (hMN : M ⊆ N)
    (hdown : ∀ j, 1 ≤ j → j ≤ q → ∀ φ : Fm, IsSigma j φ → ∀ v, ValIn M (fv φ) v →
      SatIn N v φ → SatIn M v φ) : ElemHat q M N := by
  refine ⟨hq, hM, hN, hMN, ?_⟩
  -- simultaneous induction on `j`: both Σ̂j and Π̂j formulas have the same truth value; the level
  -- `j = 0` only serves as the base of that induction, it is not part of Definition 14.1
  suffices H : ∀ j ≤ q, (∀ φ : Fm, IsSigma j φ → ∀ v, ValIn M (fv φ) v → (SatIn M v φ ↔ SatIn N v φ)) ∧
      (∀ φ : Fm, IsPi j φ → ∀ v, ValIn M (fv φ) v → (SatIn M v φ ↔ SatIn N v φ)) by
    intro j _ hj φ hφ v hv
    rcases hφ with hφ | hφ
    · exact (H j hj).1 φ hφ v hv
    · exact (H j hj).2 φ hφ v hv
  intro j
  induction j with
  | zero =>
    intro _
    constructor
    · rintro φ (⟨h⟩) v hv
      exact h.satIn_iff_satIn hM hN hMN hv
    · rintro φ (⟨h⟩) v hv
      exact h.satIn_iff_satIn hM hN hMN hv
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    -- as in the proof of Theorem 14.4, the Σ̂(j+1) agreement is established first, in *both*
    -- directions, and the Π̂(j+1) case is then reduced to it by dualization
    have hsig : ∀ φ : Fm, IsSigma (j + 1) φ → ∀ v, ValIn M (fv φ) v →
        (SatIn M v φ ↔ SatIn N v φ) := by
      intro φ hφ v hv
      constructor
      · -- upward: a witness in `M` is a witness in `N`, using the IH for the Π̂j matrix
        cases hφ with
        | succ l hl hnd hψ =>
          exact sat_exs_mono hMN l (fun w hw h => (ih'.2 _ hψ w hw).mp h) v hv
      · exact hdown (j + 1) (by omega) hj φ hφ v hv
    refine ⟨hsig, ?_⟩
    -- Π̂(j+1): by Lemma 12.2 the negation of `φ` is equivalent to a Σ̂(j+1) formula `ψ` with the
    -- same free variables, and `hsig` applied to `ψ` gives the agreement on `φ`
    intro φ hφ v hv
    obtain ⟨ψ, hψ, hfv, hequiv⟩ := hφ.exists_neg
    have h := hsig ψ hψ v (by rwa [hfv])
    exact not_iff_not.mp (((hequiv _ v).symm.trans h).trans (hequiv _ v))

end BM4.ST

namespace BM4.ST

open Fm

/-- Full elementarity `M ≺ N` (all formulas, parameters in `M`). -/
def ElemFull (M N : ZFSet.{u}) : Prop :=
  M ⊆ N ∧ ∀ (φ : Fm) (v : ℕ → ZFSet.{u}), (∀ x ∈ fv φ, v x ∈ M) → (SatIn M v φ ↔ SatIn N v φ)

theorem ElemFull.elemHat {M N : ZFSet.{u}} (h : ElemFull M N) (hM : M.IsTransitive)
    (hN : N.IsTransitive) {q : ℕ} (hq : 1 ≤ q) : ElemHat q M N :=
  ⟨hq, hM, hN, h.1, fun _ _ _ φ _ v hv => h.2 φ v hv⟩

/-- **Tarski–Vaught criterion** for full elementarity: if `M ⊆ N` and every existential statement
with parameters in `M` true in `N` has a witness in `M` (evaluated in `N`), then `M ≺ N`. -/
theorem elemFull_of_witness {M N : ZFSet.{u}} (hMN : M ⊆ N)
    (hw : ∀ (φ : Fm) (i : ℕ) (v : ℕ → ZFSet.{u}), (∀ x ∈ (fv φ).erase i, v x ∈ M) →
      (∃ x ∈ N, SatIn N (Function.update v i x) φ) → ∃ x ∈ M, SatIn N (Function.update v i x) φ) :
    ElemFull M N := by
  refine ⟨hMN, ?_⟩
  intro φ
  induction φ with
  | falsum => intro v _; rfl
  | eq i j => intro v _; rfl
  | mem i j => intro v _; rfl
  | imp φ ψ ihφ ihψ =>
    intro v hv
    simp only [fv, Finset.mem_union] at hv
    exact imp_congr (ihφ v (fun x hx => hv x (Or.inl hx))) (ihψ v (fun x hx => hv x (Or.inr hx)))
  | all i φ ih =>
    intro v hv
    simp only [SatIn, sat_all] at ih ⊢
    have hupd : ∀ x ∈ M, ∀ y ∈ fv φ, Function.update v i x y ∈ M := by
      intro x hx y hy
      by_cases hyi : y = i
      · subst hyi; simpa
      · rw [Function.update_of_ne hyi]; exact hv y (by simp [fv, Finset.mem_erase, hyi, hy])
    constructor
    · intro H
      by_contra hN
      push Not at hN
      obtain ⟨x, hxN, hx⟩ := hN
      -- `∃ x ∈ N, ¬φ` holds in `N`; get a witness in `M`
      have hex : ∃ x ∈ N, SatIn N (Function.update v i x) (Fm.not φ) := ⟨x, hxN, hx⟩
      obtain ⟨y, hyM, hy⟩ := hw (Fm.not φ) i v (by
        intro z hz
        rw [fv_not] at hz
        exact hv z (by simpa [fv] using hz)) hex
      simp only [SatIn, sat_not] at hy
      exact hy ((ih _ (hupd y hyM)).mp (H y hyM))
    · intro H x hx
      exact (ih _ (hupd x hx)).mpr (H x (hMN hx))

end BM4.ST
