/-
  The internal admissibility predicate is correct without side conditions:
  the hierarchy code required by `admP_iff` exists by Lemma 10.5(2).
-/
import Bm4.SetTheory.AdmP
import Bm4.SetTheory.LCodeEx

universe u

namespace BM4.ST

/-- **Lemma 11.2**, unconditional form. -/
theorem admP_iff' {θ η : Ordinal.{u}} (hθ : IsAdmissible θ) (hη : η < θ) :
    AdmP (· ∈ L θ) (L Ordinal.omega0.{u}) ωZ.{u} η.toZFSet ↔ IsAdmissible η :=
  admP_iff hθ hη (lcode_exists_in_L hθ hη)

end BM4.ST
