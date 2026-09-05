/-
  Part III, §13: the Δ₀ truth predicates `Tr⁺` (Σ₁) and `Tr⁻` (Π₁) via satisfaction codes.
-/
import Bm4.SetTheory.SatCode
import Bm4.SetTheory.BFCode
import Bm4.SetTheory.BFCodeD
import Bm4.SetTheory.Blk

universe u

namespace BM4.ST

open Fm

/-- The matrix of the Δ₀ truth predicates: `A` is transitive with `∅ ∈ A`, `a` is an `A`-valued
assignment, `(U, T)` is a satisfaction code for `A`, and `⟨e, b⟩` is in the truth part for the
`∅`-padding `b` of `a` that is an appropriate assignment for `e`.  Padding does not change any
value of the assignment (`seqVal_of_isPadOf`), and it is available because `∅ ∈ A`. -/
def TrD0Mat (h w e a A U T : ZFSet.{u}) : Prop :=
  A.IsTransitive ∧ ∅ ∈ A ∧ IsSeqA w A a ∧ a ∈ U ∧ SatCode h w A U T ∧
    ∃ b ∈ U, IsPadOf a b ∧ IsAsn h w A e b ∧ ZFSet.pair e b ∈ T

/-- `Tr⁺_{Δ₀}` (Definition 13.2, positive form).  The first conjunct is the paper's
"`e` is the code of a Δ₀ formula"; without it the predicate would speak about codes of
nothing. -/
def TrD0P (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) : Prop :=
  IsDelta0CodeW h w e ∧
    ∃ A, D A ∧ ∃ U, D U ∧ ∃ T, D T ∧ TrD0Mat h w e a A U T

/-- `Tr⁻_{Δ₀}` (Definition 13.2, negative form).  The code guard is the same conjunct as in
`TrD0P`; without it the universally quantified form would be vacuously true on an `e` that
codes nothing. -/
def TrD0N (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) : Prop :=
  IsDelta0CodeW h w e ∧
    ∀ A, D A → ∀ U, D U → ∀ T, D T →
    (A.IsTransitive ∧ ∅ ∈ A ∧ IsSeqA w A a ∧ a ∈ U ∧ SatCode h w A U T) →
      ∃ b ∈ U, IsPadOf a b ∧ IsAsn h w A e b ∧ ZFSet.pair e b ∈ T

theorem trD0P_imp_trD0N_of_unique {D : ZFSet.{u} → Prop} {h w e a : ZFSet.{u}}
    (huniq : ∀ A U T U' T', TrD0Mat h w e a A U T →
      (A.IsTransitive ∧ ∅ ∈ A ∧ IsSeqA w A a ∧ a ∈ U' ∧ SatCode h w A U' T') →
      ∃ b ∈ U', IsPadOf a b ∧ IsAsn h w A e b ∧ ZFSet.pair e b ∈ T')
    (hone : ∀ A A' U U' T T', D A → D A' → TrD0Mat h w e a A U T →
      (A'.IsTransitive ∧ ∅ ∈ A' ∧ IsSeqA w A' a ∧ a ∈ U' ∧ SatCode h w A' U' T') →
      ∃ b ∈ U', IsPadOf a b ∧ IsAsn h w A' e b ∧ ZFSet.pair e b ∈ T') :
    TrD0P D h w e a → TrD0N D h w e a := by
  rintro ⟨hcode, A, hA, U, hU, T, hT, hmat⟩
  refine ⟨hcode, ?_⟩
  intro A' hA' U' hU' T' hT' hpre
  exact hone A A' U U' T T' hA hA' hmat hpre

/-! ### Δ₀-definability of the matrix -/

section Delta0

variable (h w e a mA mU mT : ℕ)

/-- The matrix as a predicate on valuations. -/
def TrD0MatP : Pred.{u} := fun _ v => TrD0Mat (v h) (v w) (v e) (v a) (v mA) (v mU) (v mT)

theorem delta0_pairMem (e a T : ℕ) (hea : e ≠ a) (heT : e ≠ T) (haT : a ≠ T) :
    Delta0Def {e, a, T} (fun _ v => ZFSet.pair (v e) (v a) ∈ v T) := by
  set m := e + a + T + 1 with hm
  have h1 := (delta0_isKPair m e a (by omega) (by omega)).bex m T (by omega)
  refine (h1.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact ⟨fun ⟨p, hp, hpe⟩ => by rw [← hpe]; exact hp, fun hp => ⟨_, hp, rfl⟩⟩
  · ext k
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    omega

theorem delta0_emptyMem (A : ℕ) : Delta0Def {A} (fun _ v => (∅ : ZFSet.{u}) ∈ v A) := by
  set m := A + 1 with hm
  have h1 := (delta0_isEmpty m).bex m A (by omega)
  refine (h1.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact ⟨fun ⟨x, hx, hxe⟩ => by rw [← hxe]; exact hx, fun hx => ⟨∅, hx, rfl⟩⟩
  · ext k
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    omega

theorem SigmaDef.of_eq {q : ℕ} {s t : Finset ℕ} {P : Pred.{u}} (hP : SigmaDef q s P)
    (hst : s = t) : SigmaDef q t P := hst ▸ hP

theorem PiDef.of_eq {q : ℕ} {s t : Finset ℕ} {P : Pred.{u}} (hP : PiDef q s P)
    (hst : s = t) : PiDef q t P := hst ▸ hP

/-- The matrix of the Δ₀ truth predicates is Δ₀. -/
theorem delta0_trD0Mat (hhw : h ≠ w) (hhe : h ≠ e) (hwe : w ≠ e) (hwa : w ≠ a) (hea : e ≠ a)
    (hA : mA = h + w + e + a + 1) (hU : mU = mA + 1) (hT : mT = mA + 2) :
    Delta0Def {h, w, e, a, mA, mU, mT} (TrD0MatP.{u} h w e a mA mU mT) := by
  subst hA; subst hU; subst hT
  have f1 := delta0_isTransitive.{u} (h + w + e + a + 1)
  have f2 := delta0_emptyMem.{u} (h + w + e + a + 1)
  have f3 := delta0_isSeqA.{u} w (h + w + e + a + 1) a (by omega) hwa (by omega)
  have f4 := Delta0Def.mem.{u} a (h + w + e + a + 1 + 1)
  have f5 := delta0_satCode.{u} h w (h + w + e + a + 1) (h + w + e + a + 1 + 1)
    (h + w + e + a + 1 + 2) hhw (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have f6 := (((delta0_isPadOf.{u} a (h + w + e + a + 1 + 3) (by omega)).and
    ((delta0_isAsn.{u} h w (h + w + e + a + 1) e (h + w + e + a + 1 + 3) hhw (by omega)
      (by omega) (by omega) (by omega) (by omega)).and
      (delta0_pairMem.{u} e (h + w + e + a + 1 + 3) (h + w + e + a + 1 + 2) (by omega)
        (by omega) (by omega)))).bex (h + w + e + a + 1 + 3) (h + w + e + a + 1 + 1)
          (by omega))
  have hall := f1.and (f2.and (f3.and (f4.and (f5.and f6))))
  refine (hall.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact Iff.rfl
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢
    omega

/-- `Tr⁺_{Δ₀}` is Σ₁. -/
theorem sigmaDef_trD0P (hhw : h ≠ w) (hhe : h ≠ e) (hwe : w ≠ e) (hwa : w ≠ a) (hea : e ≠ a) :
    SigmaDef 1 {h, w, e, a} (fun D v => TrD0P.{u} D (v h) (v w) (v e) (v a)) := by
  set mA := h + w + e + a + 1 with hmA
  have hmat := (delta0_trD0Mat h w e a mA (mA + 1) (mA + 2) hhw hhe hwe hwa hea
    rfl rfl rfl).sigma 1
  have h1 := hmat.ex (mA + 2) le_rfl
  have h2 := h1.ex (mA + 1) le_rfl
  have h3 := h2.ex mA le_rfl
  have hg := (delta0_isDelta0CodeW.{u} h w e hhw hhe hwe).sigma 1
  refine ((hg.and h3).congr ?_).of_eq ?_
  · intro D v _ _
    simp only [TrD0P, TrD0MatP]
    apply and_congr_right; intro _
    apply exists_congr; intro xA; apply and_congr_right; intro _
    apply exists_congr; intro xU; apply and_congr_right; intro _
    apply exists_congr; intro xT; apply and_congr_right; intro _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · ext k
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
    omega

/-- `Tr⁻_{Δ₀}` is Π₁. -/
theorem piDef_trD0N (hhw : h ≠ w) (hhe : h ≠ e) (hwe : w ≠ e) (hwa : w ≠ a) (hea : e ≠ a) :
    PiDef 1 {h, w, e, a} (fun D v => TrD0N.{u} D (v h) (v w) (v e) (v a)) := by
  set mA := h + w + e + a + 1 with hmA
  have f1 := delta0_isTransitive.{u} mA
  have f2 := delta0_emptyMem.{u} mA
  have f3 := delta0_isSeqA.{u} w mA a (by omega) hwa (by omega)
  have f4 := Delta0Def.mem.{u} a (mA + 1)
  have f5 := delta0_satCode.{u} h w mA (mA + 1) (mA + 2) hhw (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have f6 := (((delta0_isPadOf.{u} a (mA + 3) (by omega)).and
    ((delta0_isAsn.{u} h w mA e (mA + 3) hhw (by omega) (by omega) (by omega) (by omega)
      (by omega)).and
      (delta0_pairMem.{u} e (mA + 3) (mA + 2) (by omega) (by omega)
        (by omega)))).bex (mA + 3) (mA + 1) (by omega))
  have hpre := (f1.and (f2.and (f3.and (f4.and f5)))).imp f6
  have h1 := (hpre.pi 1).all (mA + 2) le_rfl
  have h2 := h1.all (mA + 1) le_rfl
  have h3 := h2.all mA le_rfl
  have hg := (delta0_isDelta0CodeW.{u} h w e hhw hhe hwe).pi 1
  refine ((hg.and h3).congr ?_).of_eq ?_
  · intro D v _ _
    simp only [TrD0N]
    apply and_congr_right; intro _
    apply forall_congr'; intro xA; apply imp_congr_right; intro _
    apply forall_congr'; intro xU; apply imp_congr_right; intro _
    apply forall_congr'; intro xT; apply imp_congr_right; intro _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    try tauto
  · ext k
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
    omega

end Delta0

/-! ### The alternating-block truth predicates (Definition 13.4) -/

/-- The Σ-side truth of a signed Δ₀ matrix code `⟨0, ⟨sg, d⟩⟩`. -/
def TrMSig (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) : Prop :=
  IsDeltaBFCodeW h w e ∧
    ∃ sg, D sg ∧ ∃ d, D d ∧ e = ZFSet.pair (natZ 0) (ZFSet.pair sg d) ∧
    ((sg = natZ 1 ∧ TrD0P D h w d a) ∨ (sg = natZ 0 ∧ ¬ TrD0N D h w d a))

/-- The Π-side truth of a signed Δ₀ matrix code. -/
def TrMPi (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) : Prop :=
  IsDeltaBFCodeW h w e ∧
    ∀ sg, D sg → ∀ d, D d → e = ZFSet.pair (natZ 0) (ZFSet.pair sg d) →
    ((sg = natZ 1 → TrD0N D h w d a) ∧ (sg = natZ 0 → ¬ TrD0P D h w d a))

mutual
/-- Truth predicate for codes of `Sig q` block formulas (Definition 13.4, Σ side). -/
def TrSigS (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, e, a => TrMSig D h w e a
  | 1, e, a => IsSigCodeWD h w 1 e ∧ ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpd a ν t b ∧ TrMSig D h w d b
  | q + 2, e, a => IsSigCodeWD h w (q + 2) e ∧ ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpd a ν t b ∧ TrPiS D h w (q + 1) d b
/-- Truth predicate for codes of `Pi q` block formulas (Definition 13.4, Π side). -/
def TrPiS (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, e, a => TrMPi D h w e a
  | 1, e, a => IsPiCodeWD h w 1 e ∧ ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpd a ν t b → TrMPi D h w d b
  | q + 2, e, a => IsPiCodeWD h w (q + 2) e ∧ ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpd a ν t b → TrSigS D h w (q + 1) d b
end

theorem trSigS_zero (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrSigS D h w 0 e a = TrMSig D h w e a := rfl

theorem trPiS_zero (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrPiS D h w 0 e a = TrMPi D h w e a := rfl

/-! ### Complexity of the truth predicates (Lemma 13.5) -/

/-- The Σ side of a signed Δ₀ matrix code is Σ₁. -/
theorem sigmaDef_trMSig (h w e a : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hha : h ≠ a)
    (hwe : w ≠ e) (hwa : w ≠ a) (hea : e ≠ a) :
    SigmaDef 1 {h, w, e, a} (fun D v => TrMSig.{u} D (v h) (v w) (v e) (v a)) := by
  set m := h + w + e + a + 1 with hm
  have g1 := (delta0_tagPair.{u} 0 e m (m + 1) (by omega) (by omega)).sigma 1
  have g2 := (delta0_isNatZ.{u} 1 m).sigma 1
  have g3 := (delta0_isNatZ.{u} 0 m).sigma 1
  have g4 := sigmaDef_trD0P.{u} h w (m + 1) a hhw (by omega) (by omega) hwa (by omega)
  have g5 := (piDef_trD0N.{u} h w (m + 1) a hhw (by omega) (by omega) hwa (by omega)).not
  have hmat := g1.and ((g2.and g4).or (g3.and g5))
  have h1 := hmat.ex (m + 1) le_rfl
  have h2 := h1.ex m le_rfl
  have hg := (delta0_isDeltaBFCodeW.{u} h w e hhw hhe hwe).sigma 1
  refine ((hg.and h2).congr ?_).of_eq ?_
  · intro D v _ _
    simp only [TrMSig]
    apply and_congr_right; intro _
    apply exists_congr; intro sg; apply and_congr_right; intro _
    apply exists_congr; intro d; apply and_congr_right; intro _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · ext k
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
    omega

/-- The Π side of a signed Δ₀ matrix code is Π₁. -/
theorem piDef_trMPi (h w e a : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hha : h ≠ a)
    (hwe : w ≠ e) (hwa : w ≠ a) (hea : e ≠ a) :
    PiDef 1 {h, w, e, a} (fun D v => TrMPi.{u} D (v h) (v w) (v e) (v a)) := by
  set m := h + w + e + a + 1 with hm
  have g1 := (delta0_tagPair.{u} 0 e m (m + 1) (by omega) (by omega)).sigma 1
  have g2 := (delta0_isNatZ.{u} 1 m).sigma 1
  have g3 := (delta0_isNatZ.{u} 0 m).sigma 1
  have g4 := piDef_trD0N.{u} h w (m + 1) a hhw (by omega) (by omega) hwa (by omega)
  have g5 := (sigmaDef_trD0P.{u} h w (m + 1) a hhw (by omega) (by omega) hwa (by omega)).not
  have hmat := g1.imp_pi ((g2.imp_pi g4).and (g3.imp_pi g5))
  have h1 := hmat.all (m + 1) le_rfl
  have h2 := h1.all m le_rfl
  have hg := (delta0_isDeltaBFCodeW.{u} h w e hhw hhe hwe).pi 1
  refine ((hg.and h2).congr ?_).of_eq ?_
  · intro D v _ _
    simp only [TrMPi]
    apply and_congr_right; intro _
    apply forall_congr'; intro sg; apply imp_congr_right; intro _
    apply forall_congr'; intro d; apply imp_congr_right; intro _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · ext k
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
    omega

theorem trSigS_one (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrSigS D h w 1 e a = (IsSigCodeWD h w 1 e ∧ ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpd a ν t b ∧ TrMSig D h w d b) := rfl

theorem trPiS_one (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrPiS D h w 1 e a = (IsPiCodeWD h w 1 e ∧ ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpd a ν t b → TrMPi D h w d b) := rfl

theorem trSigS_add_two (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (q : ℕ) (e a : ZFSet.{u}) :
    TrSigS D h w (q + 2) e a = (IsSigCodeWD h w (q + 2) e ∧
      ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpd a ν t b ∧
        TrPiS D h w (q + 1) d b) := rfl

theorem trPiS_add_two (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (q : ℕ) (e a : ZFSet.{u}) :
    TrPiS D h w (q + 2) e a = (IsPiCodeWD h w (q + 2) e ∧
      ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpd a ν t b →
        TrSigS D h w (q + 1) d b) := rfl

/-- **Lemma 13.5**: the truth predicate for `Sig q` codes is Σ̂q (Σ̂₁ for `q ≤ 1`), and the one
for `Pi q` codes is Π̂q (Π̂₁ for `q ≤ 1`). -/
theorem trComplexity : ∀ q : ℕ, ∀ h w e a : ℕ, h ≠ w → h ≠ e → h ≠ a → w ≠ e → w ≠ a → e ≠ a →
    SigmaDef (max q 1) {h, w, e, a} (fun D v => TrSigS.{u} D (v h) (v w) q (v e) (v a)) ∧
    PiDef (max q 1) {h, w, e, a} (fun D v => TrPiS.{u} D (v h) (v w) q (v e) (v a)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro h w e a hhw hhe hha hwe hwa hea
  match q with
  | 0 =>
    exact ⟨sigmaDef_trMSig h w e a hhw hhe hha hwe hwa hea,
      piDef_trMPi h w e a hhw hhe hha hwe hwa hea⟩
  | 1 =>
    set m := h + w + e + a + 1 with hm
    constructor
    · have g1 := (delta0_tagPair.{u} 1 e m (m + 1) (by omega) (by omega)).sigma 1
      have g2 := (delta0_isBlkUpd.{u} a m (m + 2) (m + 3) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).sigma 1
      have g3 := sigmaDef_trMSig.{u} h w (m + 1) (m + 3) hhw (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hmat := g1.and (g2.and g3)
      have s4 := (((hmat.ex (m + 3) le_rfl).ex (m + 2) le_rfl).ex (m + 1) le_rfl).ex m le_rfl
      have gc := (delta0_isSigCodeWD.{u} 1 h w e hhw hhe hwe).sigma 1
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trSigS_one]
        apply and_congr_right; intro _
        apply exists_congr; intro ν; apply and_congr_right; intro _
        apply exists_congr; intro d; apply and_congr_right; intro _
        apply exists_congr; intro t; apply and_congr_right; intro _
        apply exists_congr; intro b; apply and_congr_right; intro _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
        omega
    · have g1 := (delta0_tagPair.{u} 2 e m (m + 1) (by omega) (by omega)).sigma 1
      have g2 := (delta0_isBlkUpd.{u} a m (m + 2) (m + 3) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).sigma 1
      have g3 := piDef_trMPi.{u} h w (m + 1) (m + 3) hhw (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hmat := g1.imp_pi (g2.imp_pi g3)
      have s4 := (((hmat.all (m + 3) le_rfl).all (m + 2) le_rfl).all (m + 1) le_rfl).all m le_rfl
      have gc := (delta0_isPiCodeWD.{u} 1 h w e hhw hhe hwe).pi 1
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trPiS_one]
        apply and_congr_right; intro _
        apply forall_congr'; intro ν; apply imp_congr_right; intro _
        apply forall_congr'; intro d; apply imp_congr_right; intro _
        apply forall_congr'; intro t; apply imp_congr_right; intro _
        apply forall_congr'; intro b; apply imp_congr_right; intro _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
        omega
  | n + 2 =>
    set m := h + w + e + a + 1 with hm
    obtain ⟨ihS, ihP⟩ := ih (n + 1) (by omega) h w (m + 1) (m + 3) hhw (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [show max (n + 1) 1 = n + 1 by omega] at ihS ihP
    rw [show max (n + 2) 1 = n + 2 by omega]
    constructor
    · have g1 := (delta0_tagPair.{u} 1 e m (m + 1) (by omega) (by omega)).pi (n + 1)
      have g2 := (delta0_isBlkUpd.{u} a m (m + 2) (m + 3) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).pi (n + 1)
      have hmat := g1.and (g2.and ihP)
      have s4 := (((hmat.ex (m + 3)).ex (m + 2) (by omega)).ex (m + 1) (by omega)).ex m (by omega)
      have gc := (delta0_isSigCodeWD.{u} (n + 2) h w e hhw hhe hwe).sigma (n + 2)
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trSigS_add_two]
        apply and_congr_right; intro _
        apply exists_congr; intro ν; apply and_congr_right; intro _
        apply exists_congr; intro d; apply and_congr_right; intro _
        apply exists_congr; intro t; apply and_congr_right; intro _
        apply exists_congr; intro b; apply and_congr_right; intro _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
        omega
    · have g1 := (delta0_tagPair.{u} 2 e m (m + 1) (by omega) (by omega)).pi (n + 1)
      have g2 := (delta0_isBlkUpd.{u} a m (m + 2) (m + 3) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).pi (n + 1)
      have hmat := g1.imp_sigma (g2.imp_sigma ihS)
      have s4 := (((hmat.all (m + 3)).all (m + 2) (by omega)).all (m + 1) (by omega)).all m
        (by omega)
      have gc := (delta0_isPiCodeWD.{u} (n + 2) h w e hhw hhe hwe).pi (n + 2)
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trPiS_add_two]
        apply and_congr_right; intro _
        apply forall_congr'; intro ν; apply imp_congr_right; intro _
        apply forall_congr'; intro d; apply imp_congr_right; intro _
        apply forall_congr'; intro t; apply imp_congr_right; intro _
        apply forall_congr'; intro b; apply imp_congr_right; intro _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
        omega

/-! ### The interface for correctness (Theorem 13.6) -/

/-- Correctness of the Δ₀ base in the domain `W`: for a Δ₀ formula and an assignment with
values in `W`, both forms of the Δ₀ truth predicate express satisfaction in `W`.
This is what Lemma 10.5(1) (existence of satisfaction codes inside an admissible `L θ`)
provides. -/
def BaseCorrect (W : ZFSet.{u}) : Prop :=
  ∀ φ : Fm, IsDelta0 φ → ∀ a, IsSeqA ωZ W a → a ∈ W →
    (TrD0P (· ∈ W) (L Ordinal.omega0) ωZ (Fm.code φ) a ↔ Sat (· ∈ W) (SeqVal a) φ) ∧
    (TrD0N (· ∈ W) (L Ordinal.omega0) ωZ (Fm.code φ) a ↔ Sat (· ∈ W) (SeqVal a) φ)

/-! ### The external universe -/

/-- A finite sequence of the external universe `V`: `IsSeqA` with the clause "every value lies
in `A`" dropped, since every set is a value of `V`. -/
def IsSeqV (w a : ZFSet.{u}) : Prop :=
  IsFunc a ∧ ∃ d ∈ w, IsDom a d

theorem isSeqV_of_isSeqA {w A a : ZFSet.{u}} (h : IsSeqA w A a) : IsSeqV w a := ⟨h.1, h.2.1⟩

/-- Correctness of the Δ₀ base in the external universe `V`, i.e. the last sentence of
**Lemma 13.3**, 「同じ同値は外部宇宙 V でも成立する」.  It is `BaseCorrect` with the domain
`(· ∈ W)` replaced by `V = fun _ => True` and the two clauses placing the assignment inside `W`
replaced by the single clause that it is a finite sequence. -/
def BaseCorrectV : Prop :=
  ∀ φ : Fm, IsDelta0 φ → ∀ a : ZFSet.{u}, IsSeqV ωZ a →
    (TrD0P (fun _ => True) (L Ordinal.omega0) ωZ (Fm.code φ) a ↔ SatV (SeqVal a) φ) ∧
    (TrD0N (fun _ => True) (L Ordinal.omega0) ωZ (Fm.code φ) a ↔ SatV (SeqVal a) φ)

end BM4.ST
