/-
  `BaseCorrect (L θ)` for admissible `θ`: the Δ₀ truth predicates of §13 are correct in `L θ`,
  using the existence of satisfaction codes inside `L θ` (Lemma 10.5(1)).

  The last sentence of Lemma 13.3 — 「同じ同値は外部宇宙 V でも成立する」 — is `baseCorrect_V`
  below: the same equivalence in the external universe, where the transitive set carrying the
  satisfaction code is built in ZFC instead of inside `L θ`.  Combined with `trSigPiS_correct_V`
  of `TrCorrect.lean` it gives the external half of Theorem 13.6 as well.
-/
import Bm4.SetTheory.SatInL
import Bm4.SetTheory.Truth
import Bm4.SetTheory.TrCorrect
import Bm4.SetTheory.LCode

universe u

namespace BM4.ST

open Fm

/-- A finite sequence over `L θ` already lives over some `L ξ` with `0 < ξ < θ`. -/
theorem isSeqA_stage {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {a : ZFSet.{u}}
    (ha : IsSeqA ωZ (L θ) a) (haL : a ∈ L θ) :
    ∃ ξ, 0 < ξ ∧ ξ < θ ∧ IsSeqA ωZ (L ξ) a ∧ a ∈ L ξ := by
  have hlim := hθ.isSuccLimit
  obtain ⟨ζ, hζ, haζ⟩ := (mem_L_limit hlim).mp haL
  refine ⟨max ζ 1, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (zero_lt_one' Ordinal.{u}) (le_max_right ζ 1)
  · refine max_lt hζ ?_
    calc (1 : Ordinal.{u}) ≤ Ordinal.omega0 := Ordinal.one_le_iff_ne_zero.mpr (by simp)
      _ < θ := hθ.omega_lt
  · have hT := L_transitive (max ζ 1)
    have haζ' : a ∈ L (max ζ 1) := L_mono (le_max_left _ _) haζ
    refine ⟨ha.1, ha.2.1, ?_⟩
    intro i x hix
    have h1 : ZFSet.pair i x ∈ L (max ζ 1) := hT.subset_of_mem haζ' hix
    have h2 : ({i, x} : ZFSet.{u}) ∈ L (max ζ 1) := hT.subset_of_mem h1 (by simp [ZFSet.pair])
    exact hT.subset_of_mem h2 (by simp)
  · exact L_mono (le_max_left _ _) haζ

/-- **`BaseCorrect (L θ)`** for admissible `θ`, i.e. **Lemma 13.3** inside `W = L θ`. -/
theorem baseCorrect_L {θ : Ordinal.{u}} (hθ : IsAdmissible θ) : BaseCorrect (L θ) := by
  have hTθ := L_transitive θ
  intro φ hφ a ha haL hcov
  -- a stage containing the sequence
  obtain ⟨ξ, -, hξ, haξ, -⟩ := isSeqA_stage hθ ha haL
  have hAmem : L ξ ∈ L θ := L_mem_L hξ
  have hAt : (L ξ).IsTransitive := L_transitive ξ
  obtain ⟨U, hU, T, hT, hcode⟩ := satCode_exists_in_L hθ hAmem
  have haU : a ∈ U := seq_mem_of_puCl hcode.trans hcode.A_mem hcode.w_mem hcode.pucl haξ
  have hasnξ : IsAsn (L Ordinal.omega0) ωZ (L ξ) φ.code a := isAsn_code_iff.mpr ⟨haξ, hcov⟩
  -- (13.3) and (13.4): any satisfaction code computes the same truth value on `a`
  have hgen : ∀ A' U' T', A'.IsTransitive → A' ∈ L θ →
      IsAsn (L Ordinal.omega0) ωZ A' φ.code a → SatCode (L Ordinal.omega0) ωZ A' U' T' →
      (ZFSet.pair φ.code a ∈ T' ↔ Sat (· ∈ L θ) (SeqVal a) φ) := by
    intro A' U' T' hA't hA' hasn hc'
    obtain ⟨ha', hcov'⟩ := isAsn_code_iff.mp hasn
    have hv : ∀ x ∈ fv φ, SeqVal a x ∈ A' := fun x hx => seqVal_mem_of_inDom ha' (hcov' x hx)
    have hvθ : ∀ x ∈ fv φ, SeqVal a x ∈ L θ := fun x hx => hTθ.subset_of_mem hA' (hv x hx)
    rw [satCode_correct hc' φ a ha' hcov', IsDelta0.satIn_iff_satV hφ hA't hv]
    exact (IsDelta0.satIn_iff_satV hφ hTθ hvθ).symm
  have hcodeD : IsDelta0CodeW (L Ordinal.omega0) ωZ φ.code :=
    (isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩
  have hkey : ZFSet.pair φ.code a ∈ T ↔ Sat (· ∈ L θ) (SeqVal a) φ :=
    hgen (L ξ) U T hAt hAmem hasnξ hcode
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- `Tr⁺` is correct
    rintro ⟨-, A', hA', U', hU', T', hT', hA't, hasn, -, hc', hmem⟩
    exact (hgen A' U' T' hA't hA' hasn hc').mp hmem
  · intro hsat
    exact ⟨hcodeD, L ξ, hAmem, U, hU, T, hT, hAt, hasnξ, haU, hcode, hkey.mpr hsat⟩
  · -- `Tr⁻` is correct: the code built above is the counterexample when `φ` fails
    intro hall
    exact hkey.mp (hall.2 (L ξ) hAmem U hU T hT ⟨hAt, hasnξ, haU, hcode⟩)
  · intro hsat
    refine ⟨hcodeD, ?_⟩
    rintro A' hA' U' hU' T' hT' ⟨hA't, hasn, -, hc'⟩
    exact (hgen A' U' T' hA't hA' hasn hc').mpr hsat

/-! ### The external universe -/

/-- **Lemma 13.3**, last sentence: the same equivalence holds in the external universe `V`.
The transitive set carrying the assignment values is a rank initial segment, and the
satisfaction code for it is `satCode_exists`, built in ZFC. -/
theorem baseCorrect_V : BaseCorrectV.{u} := by
  intro φ hφ a ha hcov
  obtain ⟨A, hAt, -, haA, -⟩ := exists_wClosed_mem a a
  have haseq : IsSeqA ωZ A a := isSeqA_of_isSeqV hAt ha haA
  obtain ⟨U, T, hcode⟩ := satCode_exists A
  have haU : a ∈ U := seq_mem_of_puCl hcode.trans hcode.A_mem hcode.w_mem hcode.pucl haseq
  have hasnA : IsAsn (L Ordinal.omega0) ωZ A φ.code a := isAsn_code_iff.mpr ⟨haseq, hcov⟩
  have hcodeD : IsDelta0CodeW (L Ordinal.omega0) ωZ φ.code :=
    (isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩
  have hgen : ∀ A' U' T', A'.IsTransitive → IsAsn (L Ordinal.omega0) ωZ A' φ.code a →
      SatCode (L Ordinal.omega0) ωZ A' U' T' →
      (ZFSet.pair φ.code a ∈ T' ↔ SatV (SeqVal a) φ) := by
    intro A' U' T' hA't hasn hc'
    obtain ⟨ha', hcov'⟩ := isAsn_code_iff.mp hasn
    have hv : ∀ x ∈ fv φ, SeqVal a x ∈ A' := fun x hx => seqVal_mem_of_inDom ha' (hcov' x hx)
    rw [satCode_correct hc' φ a ha' hcov']
    exact IsDelta0.satIn_iff_satV hφ hA't hv
  have hkey : ZFSet.pair φ.code a ∈ T ↔ SatV (SeqVal a) φ := hgen A U T hAt hasnA hcode
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨-, A', -, U', -, T', -, hA't, hasn, -, hc', hmem⟩
    exact (hgen A' U' T' hA't hasn hc').mp hmem
  · intro hsat
    exact ⟨hcodeD, A, trivial, U, trivial, T, trivial, hAt, hasnA, haU, hcode, hkey.mpr hsat⟩
  · intro hall
    exact hkey.mp (hall.2 A trivial U trivial T trivial ⟨hAt, hasnA, haU, hcode⟩)
  · intro hsat
    refine ⟨hcodeD, ?_⟩
    rintro A' - U' - T' - ⟨hA't, hasn, -, hc'⟩
    exact (hgen A' U' T' hA't hasn hc').mpr hsat

end BM4.ST
