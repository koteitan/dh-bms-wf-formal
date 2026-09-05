/-
  Part III (§15): the stability relation `α ◁ₖ β` between admissible ordinals, and the
  properties required by `LabelSystem` (Lemma 15.1 and the initial pair of Lemma 16.2).
-/
import Bm4.SetTheory.AdmTrans

universe u

namespace BM4.ST

open Fm

/-- Admissible ordinals. -/
def AdmOrd : Type (u + 1) := {α : Ordinal.{u} // IsAdmissible α}

namespace AdmOrd

noncomputable instance : LinearOrder AdmOrd.{u} := Subtype.instLinearOrder _

instance : WellFoundedLT AdmOrd.{u} :=
  ⟨(Subtype.strictMono_coe (fun α : Ordinal.{u} => IsAdmissible α)).wellFoundedLT.wf⟩

theorem lt_def {α β : AdmOrd.{u}} : α < β ↔ α.1 < β.1 := Iff.rfl

end AdmOrd

/-- The stability relation `α ◁ₖ β` of the paper (15.1): `L α ≺*_{k+2} L β`. -/
def RelAdm (k : ℕ) (α β : AdmOrd.{u}) : Prop :=
  α < β ∧ ElemHat (k + 2) (L α.1) (L β.1)

theorem relAdm_lt {k : ℕ} {α β : AdmOrd.{u}} (h : RelAdm k α β) : α < β := h.1

/-- Lemma 15.1 (1). -/
theorem relAdm_mono {h k : ℕ} {α β : AdmOrd.{u}} (hhk : h ≤ k) (hr : RelAdm k α β) :
    RelAdm h α β :=
  ⟨hr.1, hr.2.mono (by omega)⟩

/-- Lemma 15.1 (2). -/
theorem relAdm_trans {k : ℕ} {α β γ : AdmOrd.{u}} (h₁ : RelAdm k α β) (h₂ : RelAdm k β γ) :
    RelAdm k α γ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Full elementarity gives `◁ₖ` for every `k`. -/
theorem relAdm_of_elemFull {α β : AdmOrd.{u}} (hlt : α < β) (h : ElemFull (L α.1) (L β.1))
    (k : ℕ) : RelAdm k α β :=
  ⟨hlt, h.elemHat (k + 2)⟩

/-- **The initial pair** (Lemma 16.2): admissible `Λ < Θ` with `Λ ◁ₖ Θ` for every `k`. -/
theorem exists_relAdm_all : ∃ Λ Θ : AdmOrd.{u}, ∀ k, RelAdm k Λ Θ := by
  obtain ⟨Λ, Θ, hΛ, hΘ, hlt, hel⟩ := exists_admissible_elemFull_pair.{u}
  exact ⟨⟨Λ, hΛ⟩, ⟨Θ, hΘ⟩, fun k => relAdm_of_elemFull (by exact hlt) hel k⟩

end BM4.ST
