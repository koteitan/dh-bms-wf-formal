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

/-- The matrix of **Definition 13.2**: `A` is transitive, `Asn_A(e, a)` holds, `a ∈ U`,
`(U, T)` is a satisfaction code for `A`, and `⟨e, a⟩` lies in its truth part. -/
def TrD0Mat (h w e a A U T : ZFSet.{u}) : Prop :=
  A.IsTransitive ∧ IsAsn h w A e a ∧ a ∈ U ∧ SatCode h w A U T ∧ ZFSet.pair e a ∈ T

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
    (A.IsTransitive ∧ IsAsn h w A e a ∧ a ∈ U ∧ SatCode h w A U T) →
      ZFSet.pair e a ∈ T

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
  have f2 := delta0_isAsn.{u} h w (h + w + e + a + 1) e a hhw hhe (by omega) hwe hwa (by omega)
  have f3 := Delta0Def.mem.{u} a (h + w + e + a + 1 + 1)
  have f4 := delta0_satCode.{u} h w (h + w + e + a + 1) (h + w + e + a + 1 + 1)
    (h + w + e + a + 1 + 2) hhw (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have f5 := delta0_pairMem.{u} e a (h + w + e + a + 1 + 2) hea (by omega) (by omega)
  have hall := f1.and (f2.and (f3.and (f4.and f5)))
  refine (hall.congr ?_).mono ?_
  · intro D v _ _
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
  have f2 := delta0_isAsn.{u} h w mA e a hhw hhe (by omega) hwe hwa (by omega)
  have f3 := Delta0Def.mem.{u} a (mA + 1)
  have f4 := delta0_satCode.{u} h w mA (mA + 1) (mA + 2) hhw (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have f5 := delta0_pairMem.{u} e a (mA + 2) hea (by omega) (by omega)
  have hpre := (f1.and (f2.and (f3.and f4))).imp f5
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

/-- The Σ-side truth of a signed Δ₀ matrix code `⟨0, ⟨sg, d⟩⟩`.

Definition 13.2 speaks only of *appropriate* assignments: `Tr⁺_{Δ₀}(d, a)` requires
`Asn_A(d, a)`, so an `a` whose domain misses a free variable of `d` is never judged.  This
layer, which the paper does not have (its Definition 13.4 uses `Tr⁺_{Δ₀}(Body(e), b)`
directly), closes that gap by judging some `∅`-padding `b` of `a` instead.  Padding leaves
every value of the assignment unchanged (`seqVal_of_isPadOf`), so the truth value is the
intended one, and the extra `∃ b` is `D`-bounded, so (13.1) is unaffected. -/
def TrMSig (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) : Prop :=
  IsDeltaBFCodeW h w e ∧
    ∃ sg, D sg ∧ ∃ d, D d ∧ e = ZFSet.pair (natZ 0) (ZFSet.pair sg d) ∧
    ∃ b, D b ∧ IsPadOf a b ∧
      ((sg = natZ 1 ∧ TrD0P D h w d b) ∨ (sg = natZ 0 ∧ ¬ TrD0N D h w d b))

/-- The Π-side truth of a signed Δ₀ matrix code, with the same `∅`-padding as `TrMSig`. -/
def TrMPi (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) : Prop :=
  IsDeltaBFCodeW h w e ∧
    ∀ sg, D sg → ∀ d, D d → e = ZFSet.pair (natZ 0) (ZFSet.pair sg d) →
    ∀ b, D b → IsPadOf a b →
      ((sg = natZ 1 → TrD0N D h w d b) ∧ (sg = natZ 0 → ¬ TrD0P D h w d b))

/-! ### Complexity of the truth predicates (Lemma 13.5) -/

/-- The Σ side of a signed Δ₀ matrix code is Σ₁. -/
theorem sigmaDef_trMSig (h w e a : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hha : h ≠ a)
    (hwe : w ≠ e) (hwa : w ≠ a) (hea : e ≠ a) :
    SigmaDef 1 {h, w, e, a} (fun D v => TrMSig.{u} D (v h) (v w) (v e) (v a)) := by
  set m := h + w + e + a + 1 with hm
  have g1 := (delta0_tagPair.{u} 0 e m (m + 1) (by omega) (by omega)).sigma 1
  have gp := (delta0_isPadOf.{u} a (m + 2) (by omega)).sigma 1
  have g2 := (delta0_isNatZ.{u} 1 m).sigma 1
  have g3 := (delta0_isNatZ.{u} 0 m).sigma 1
  have g4 := sigmaDef_trD0P.{u} h w (m + 1) (m + 2) hhw (by omega) (by omega) (by omega)
    (by omega)
  have g5 := (piDef_trD0N.{u} h w (m + 1) (m + 2) hhw (by omega) (by omega) (by omega)
    (by omega)).not
  have hb := (gp.and ((g2.and g4).or (g3.and g5))).ex (m + 2) le_rfl
  have hmat := g1.and hb
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
  have gp := (delta0_isPadOf.{u} a (m + 2) (by omega)).sigma 1
  have g2 := (delta0_isNatZ.{u} 1 m).sigma 1
  have g3 := (delta0_isNatZ.{u} 0 m).sigma 1
  have g4 := piDef_trD0N.{u} h w (m + 1) (m + 2) hhw (by omega) (by omega) (by omega)
    (by omega)
  have g5 := (sigmaDef_trD0P.{u} h w (m + 1) (m + 2) hhw (by omega) (by omega) (by omega)
    (by omega)).not
  have hb := (gp.imp_pi ((g2.imp_pi g4).and (g3.imp_pi g5))).all (m + 2) le_rfl
  have hmat := g1.imp_pi hb
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

/-! ### The interface for correctness (Theorem 13.6) -/

/-- **Lemma 13.3** as an interface: for a Δ₀ formula `φ`, an assignment `a ∈ W` with values in
`W` that is *appropriate* for `φ` (its domain covers every free variable), both forms of the Δ₀
truth predicate express satisfaction in `W`.  This is what Lemma 10.5(1) (existence of
satisfaction codes inside an admissible `L θ`) provides. -/
def BaseCorrect (W : ZFSet.{u}) : Prop :=
  ∀ φ : Fm, IsDelta0 φ → ∀ a, IsSeqA ωZ W a → a ∈ W →
    (∀ k ∈ Fm.fv φ, InDomZ a (natZ k)) →
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
replaced by the single clause that it is a finite sequence.  The paper's hypothesis that `a`
is an appropriate assignment is kept. -/
def BaseCorrectV : Prop :=
  ∀ φ : Fm, IsDelta0 φ → ∀ a : ZFSet.{u}, IsSeqV ωZ a →
    (∀ k ∈ Fm.fv φ, InDomZ a (natZ k)) →
    (TrD0P (fun _ => True) (L Ordinal.omega0) ωZ (Fm.code φ) a ↔ SatV (SeqVal a) φ) ∧
    (TrD0N (fun _ => True) (L Ordinal.omega0) ωZ (Fm.code φ) a ↔ SatV (SeqVal a) φ)

end BM4.ST
