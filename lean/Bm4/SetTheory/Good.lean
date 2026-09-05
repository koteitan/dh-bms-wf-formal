/-
  The interface an admissible ordinal must satisfy for the internal predicates of §13–15 to be
  correct: satisfaction codes and hierarchy codes exist inside `L θ`.
-/
import Bm4.SetTheory.TrCorrect
import Bm4.SetTheory.LCode
import Bm4.SetTheory.Stable

universe u

namespace BM4.ST

open Fm

/-- `θ` is *good*: admissible, with the Δ₀ truth predicates correct in `L θ` and with a code for
every `L ξ`, `ξ < θ`, inside `L θ`. -/
structure GoodOrd (θ : Ordinal.{u}) : Prop where
  adm : IsAdmissible θ
  base : BaseCorrect (L θ)
  lcode : ∀ ξ < θ, ∃ M ∈ L θ, ∃ c ∈ L θ, LCode (L Ordinal.omega0) ωZ ξ.toZFSet M c

namespace GoodOrd

variable {θ : Ordinal.{u}}

theorem isSuccLimit (hθ : GoodOrd θ) : Order.IsSuccLimit θ := hθ.adm.isSuccLimit

theorem transitive (_hθ : GoodOrd θ) : (L θ).IsTransitive := L_transitive θ

theorem wClosed (hθ : GoodOrd θ) : WClosed (L θ) := wClosed_L hθ.adm.isSuccLimit

theorem omega_lt (hθ : GoodOrd θ) : Ordinal.omega0 < θ := hθ.adm.omega_lt

/-- `L ω ∈ L θ`. -/
theorem Lomega_mem (hθ : GoodOrd θ) : L Ordinal.omega0.{u} ∈ L θ := L_mem_L hθ.adm.omega_lt

/-- `ωZ ∈ L θ`. -/
theorem omegaZ_mem (hθ : GoodOrd θ) : ωZ.{u} ∈ L θ := hθ.adm.omega_mem

/-- The code of an ordinal below `θ` lies in `L θ`. -/
theorem toZFSet_mem (_hθ : GoodOrd θ) {ξ : Ordinal.{u}} (h : ξ < θ) : ξ.toZFSet ∈ L θ :=
  (toZFSet_mem_L_iff θ ξ).mpr h

/-- The unique set coded for `ξ < θ` is `L ξ`. -/
theorem lcode_L (hθ : GoodOrd θ) {ξ : Ordinal.{u}} (h : ξ < θ) :
    ∃ c ∈ L θ, LCode (L Ordinal.omega0) ωZ ξ.toZFSet (L ξ) c := by
  obtain ⟨M, hM, c, hc, hcode⟩ := hθ.lcode ξ h
  refine ⟨c, hc, ?_⟩
  rwa [lcode_sound hcode] at hcode

/-- `L ξ ∈ L θ` for `ξ < θ`. -/
theorem L_mem (_hθ : GoodOrd θ) {ξ : Ordinal.{u}} (h : ξ < θ) : L ξ ∈ L θ := L_mem_L h

end GoodOrd

end BM4.ST
