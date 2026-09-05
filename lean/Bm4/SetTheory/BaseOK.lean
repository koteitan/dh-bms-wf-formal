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

/-- **`BaseCorrect (L θ)`** for admissible `θ`. -/
theorem baseCorrect_L {θ : Ordinal.{u}} (hθ : IsAdmissible θ) : BaseCorrect (L θ) := by
  have hlim := hθ.isSuccLimit
  have hTθ := L_transitive θ
  intro φ hφ a ha haL
  -- a stage containing the sequence
  obtain ⟨ξ, hξ0, hξ, haξ, haLξ⟩ := isSeqA_stage hθ ha haL
  have hAmem : L ξ ∈ L θ := L_mem_L hξ
  have hAt : (L ξ).IsTransitive := L_transitive ξ
  have hemp : (∅ : ZFSet.{u}) ∈ L ξ := empty_mem_L hξ0
  obtain ⟨U, hU, T, hT, hcode⟩ := satCode_exists_in_L hθ hAmem
  -- the `∅`-padding of `a` covering the free variables of `φ`
  obtain ⟨a₁, ha₁, hpad₁, hval₁, hdom₁⟩ := exists_padSeq haξ hemp (fvSup φ)
  have hcov₁ : ∀ k ∈ fv φ, InDomZ a₁ (natZ k) := fun k hk => hdom₁ k (lt_fvSup hk)
  have ha₁U : a₁ ∈ U := seq_mem_of_puCl hcode.trans hcode.A_mem hcode.w_mem hcode.pucl ha₁
  -- any satisfaction code computes the same truth value on a padding of `a`
  have hgen : ∀ A' U' T' b, A'.IsTransitive → ∅ ∈ A' → A' ∈ L θ → IsSeqA ωZ A' a →
      SatCode (L Ordinal.omega0) ωZ A' U' T' → IsPadOf a b → IsAsn (L Ordinal.omega0) ωZ A' φ.code b →
      b ∈ U' → (ZFSet.pair φ.code b ∈ T' ↔ Sat (· ∈ L θ) (SeqVal a) φ) := by
    intro A' U' T' b hA't hemp' hA' ha' hc' hpad hasn hbU
    obtain ⟨hbseq, hbcov⟩ := isAsn_code_iff.mp hasn
    have hbval : SeqVal b = SeqVal a := seqVal_of_isPadOf ha'.1 hbseq.1 hpad
    have habs' : SatIn A' (SeqVal a) φ ↔ Sat (· ∈ L θ) (SeqVal a) φ := by
      have hv : ∀ x ∈ fv φ, SeqVal a x ∈ A' := fun x hx => by
        rw [← hbval]; exact seqVal_mem_of_inDom hbseq (hbcov x hx)
      have hvθ : ∀ x ∈ fv φ, SeqVal a x ∈ L θ := fun x hx => hTθ.subset_of_mem hA' (hv x hx)
      rw [IsDelta0.satIn_iff_satV hφ hA't hv]
      exact (IsDelta0.satIn_iff_satV hφ hTθ hvθ).symm
    rw [satCode_correct hc' φ b hbseq hbcov hbU, hbval]
    exact habs'
  have hcodeD : IsDelta0CodeW (L Ordinal.omega0) ωZ φ.code :=
    (isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩
  have hkey : ZFSet.pair φ.code a₁ ∈ T ↔ Sat (· ∈ L θ) (SeqVal a) φ :=
    hgen (L ξ) U T a₁ hAt hemp hAmem haξ hcode hpad₁ (isAsn_code_iff.mpr ⟨ha₁, hcov₁⟩) ha₁U
  constructor
  · -- `Tr⁺`
    constructor
    · rintro ⟨-, A', hA', U', hU', T', hT', hA't, hemp', ha', ha'U, hc', b, hbU, hpad, hasn,
        hmem'⟩
      exact (hgen A' U' T' b hA't hemp' hA' ha' hc' hpad hasn hbU).mp hmem'
    · intro hsat
      exact ⟨hcodeD, L ξ, hAmem, U, hU, T, hT, hAt, hemp, haξ,
        seq_mem_of_puCl hcode.trans hcode.A_mem hcode.w_mem hcode.pucl haξ, hcode,
        a₁, ha₁U, hpad₁, isAsn_code_iff.mpr ⟨ha₁, hcov₁⟩, hkey.mpr hsat⟩
  · -- `Tr⁻`
    constructor
    · intro hall
      obtain ⟨b, hbU, hpad, hasn, hmem⟩ := hall.2 (L ξ) hAmem U hU T hT
        ⟨hAt, hemp, haξ, seq_mem_of_puCl hcode.trans hcode.A_mem hcode.w_mem hcode.pucl haξ,
          hcode⟩
      exact (hgen (L ξ) U T b hAt hemp hAmem haξ hcode hpad hasn hbU).mp hmem
    · intro hsat
      refine ⟨hcodeD, ?_⟩
      intro A' hA' U' hU' T' hT' ⟨hA't, hemp', ha', ha'U, hc'⟩
      obtain ⟨b, hb, hbpad, hbval, hbdom⟩ := exists_padSeq ha' hemp' (fvSup φ)
      have hbcov : ∀ k ∈ fv φ, InDomZ b (natZ k) := fun k hk => hbdom k (lt_fvSup hk)
      have hbU : b ∈ U' := seq_mem_of_puCl hc'.trans hc'.A_mem hc'.w_mem hc'.pucl hb
      have hasn : IsAsn (L Ordinal.omega0) ωZ A' φ.code b := isAsn_code_iff.mpr ⟨hb, hbcov⟩
      exact ⟨b, hbU, hbpad, hasn,
        (hgen A' U' T' b hA't hemp' hA' ha' hc' hbpad hasn hbU).mpr hsat⟩

/-! ### The external universe -/

/-- **Lemma 13.3**, last sentence: the same equivalence holds in the external universe `V`.
The transitive set carrying the assignment values is a rank initial segment, and the
satisfaction code for it is `satCode_exists`, built in ZFC. -/
theorem baseCorrect_V : BaseCorrectV.{u} := by
  intro φ hφ a ha
  obtain ⟨A, hAt, hAcl, haA, -⟩ := exists_wClosed_mem a a
  have hemp : (∅ : ZFSet.{u}) ∈ A := hAcl.empty_mem
  have haseq : IsSeqA ωZ A a := isSeqA_of_isSeqV hAt ha haA
  obtain ⟨U, T, hcode⟩ := satCode_exists A
  obtain ⟨a₁, ha₁, hpad₁, hval₁, hdom₁⟩ := exists_padSeq haseq hemp (fvSup φ)
  have hcov₁ : ∀ k ∈ fv φ, InDomZ a₁ (natZ k) := fun k hk => hdom₁ k (lt_fvSup hk)
  have ha₁U : a₁ ∈ U := seq_mem_of_puCl hcode.trans hcode.A_mem hcode.w_mem hcode.pucl ha₁
  have haU : a ∈ U := seq_mem_of_puCl hcode.trans hcode.A_mem hcode.w_mem hcode.pucl haseq
  have hcodeD : IsDelta0CodeW (L Ordinal.omega0) ωZ φ.code :=
    (isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩
  -- any satisfaction code computes the same truth value on a padding of `a`
  have hgen : ∀ A' U' T' b, A'.IsTransitive → (∅ : ZFSet.{u}) ∈ A' → IsSeqA ωZ A' a →
      SatCode (L Ordinal.omega0) ωZ A' U' T' → IsPadOf a b →
      IsAsn (L Ordinal.omega0) ωZ A' φ.code b → b ∈ U' →
      (ZFSet.pair φ.code b ∈ T' ↔ SatV (SeqVal a) φ) := by
    intro A' U' T' b hA't hemp' ha' hc' hpad hasn hbU
    obtain ⟨hbseq, hbcov⟩ := isAsn_code_iff.mp hasn
    have hbval : SeqVal b = SeqVal a := seqVal_of_isPadOf ha'.1 hbseq.1 hpad
    have hv : ∀ x ∈ fv φ, SeqVal a x ∈ A' := fun x hx => by
      rw [← hbval]; exact seqVal_mem_of_inDom hbseq (hbcov x hx)
    rw [satCode_correct hc' φ b hbseq hbcov hbU, hbval]
    exact IsDelta0.satIn_iff_satV hφ hA't hv
  have hkey : ZFSet.pair φ.code a₁ ∈ T ↔ SatV (SeqVal a) φ :=
    hgen A U T a₁ hAt hemp haseq hcode hpad₁ (isAsn_code_iff.mpr ⟨ha₁, hcov₁⟩) ha₁U
  constructor
  · -- `Tr⁺`
    constructor
    · rintro ⟨-, A', -, U', -, T', -, hA't, hemp', ha', ha'U, hc', b, hbU, hpad, hasn, hmem'⟩
      exact (hgen A' U' T' b hA't hemp' ha' hc' hpad hasn hbU).mp hmem'
    · intro hsat
      exact ⟨hcodeD, A, trivial, U, trivial, T, trivial, hAt, hemp, haseq, haU, hcode,
        a₁, ha₁U, hpad₁, isAsn_code_iff.mpr ⟨ha₁, hcov₁⟩, hkey.mpr hsat⟩
  · -- `Tr⁻`
    constructor
    · intro hall
      obtain ⟨b, hbU, hpad, hasn, hmem⟩ :=
        hall.2 A trivial U trivial T trivial ⟨hAt, hemp, haseq, haU, hcode⟩
      exact (hgen A U T b hAt hemp haseq hcode hpad hasn hbU).mp hmem
    · intro hsat
      refine ⟨hcodeD, ?_⟩
      rintro A' - U' - T' - ⟨hA't, hemp', ha', ha'U, hc'⟩
      obtain ⟨b, hb, hbpad, hbval, hbdom⟩ := exists_padSeq ha' hemp' (fvSup φ)
      have hbcov : ∀ k ∈ fv φ, InDomZ b (natZ k) := fun k hk => hbdom k (lt_fvSup hk)
      have hbU : b ∈ U' := seq_mem_of_puCl hc'.trans hc'.A_mem hc'.w_mem hc'.pucl hb
      have hasn : IsAsn (L Ordinal.omega0) ωZ A' φ.code b := isAsn_code_iff.mpr ⟨hb, hbcov⟩
      exact ⟨b, hbU, hbpad, hasn, (hgen A' U' T' b hA't hemp' ha' hc' hbpad hasn hbU).mpr hsat⟩

/-- **Theorem 13.6** (Σ side), last sentence: the equivalence in the external universe `V`. -/
theorem trSigS_correct_ext :
    ∀ (q : ℕ) (b : BF), BF.Sig q b → ∀ a : ZFSet.{u}, GoodAsnV b a →
      (TrSigS (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        SatV (SeqVal a) b.toFm) :=
  trSigS_correct_V baseCorrect_V

/-- **Theorem 13.6** (Π side), last sentence: the equivalence in the external universe `V`. -/
theorem trPiS_correct_ext :
    ∀ (q : ℕ) (b : BF), BF.Pi q b → ∀ a : ZFSet.{u}, GoodAsnV b a →
      (TrPiS (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        SatV (SeqVal a) b.toFm) :=
  trPiS_correct_V baseCorrect_V

end BM4.ST
