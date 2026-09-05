/-
  Part III, §13 over the *padding* block update of §12.

  `Truth.lean` and `TrCorrect.lean` build the alternating-block truth predicates on
  `IsBlkUpd`, whose block variables must already lie in the domain of the assignment; that
  requirement reappears in `GoodAsn` as the clause
  `∀ i ∈ b.blockVars, ∃ y, ⟨natZ i, y⟩ ∈ a`.

  Here the same development is carried out over `IsBlkUpdP` of `BlkP.lean`, which pads the
  domain up to `max (dom a) {ν i + 1}`.  The padding is exactly what makes that clause
  superfluous, so `GoodAsnP` has one clause fewer than `GoodAsn`.
-/
import Bm4.SetTheory.TrCorrect
import Bm4.SetTheory.BFCodeD
import Bm4.SetTheory.BlkP

universe u

namespace BM4.ST

open Fm

/-! ### The alternating-block truth predicates (Definition 13.4, padding form) -/

mutual
/-- Truth predicate for codes of `Sig q` block formulas, over the padding block update. -/
def TrSigP (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, e, a => TrMSig D h w e a
  | 1, e, a => IsSigCodeWD h w 1 e ∧ ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpdP w a ν t b ∧ TrMSig D h w d b
  | q + 2, e, a => IsSigCodeWD h w (q + 2) e ∧ ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpdP w a ν t b ∧ TrPiP D h w (q + 1) d b
/-- Truth predicate for codes of `Pi q` block formulas, over the padding block update. -/
def TrPiP (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, e, a => TrMPi D h w e a
  | 1, e, a => IsPiCodeWD h w 1 e ∧ ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpdP w a ν t b → TrMPi D h w d b
  | q + 2, e, a => IsPiCodeWD h w (q + 2) e ∧ ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpdP w a ν t b → TrSigP D h w (q + 1) d b
end

theorem trSigP_zero (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrSigP D h w 0 e a = TrMSig D h w e a := rfl

theorem trPiP_zero (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrPiP D h w 0 e a = TrMPi D h w e a := rfl

theorem trSigP_one (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrSigP D h w 1 e a = (IsSigCodeWD h w 1 e ∧ ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpdP w a ν t b ∧ TrMSig D h w d b) := rfl

theorem trPiP_one (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrPiP D h w 1 e a = (IsPiCodeWD h w 1 e ∧ ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpdP w a ν t b → TrMPi D h w d b) := rfl

theorem trSigP_add_two (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (q : ℕ) (e a : ZFSet.{u}) :
    TrSigP D h w (q + 2) e a = (IsSigCodeWD h w (q + 2) e ∧
      ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpdP w a ν t b ∧
        TrPiP D h w (q + 1) d b) := rfl

theorem trPiP_add_two (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (q : ℕ) (e a : ZFSet.{u}) :
    TrPiP D h w (q + 2) e a = (IsPiCodeWD h w (q + 2) e ∧
      ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpdP w a ν t b →
        TrSigP D h w (q + 1) d b) := rfl

/-! ### `Vars` and `Body` as terms (Definition 13.4) -/

/-
  Definition 13.4 writes the two code projections `ν = Vars(e)` and `d = Body(e)` as terms of
  the definitional extension by `Δ₀`-definable function symbols, and quantifies only over `t`
  and `b`.  `TrSigP` and `TrPiP` instead quantify over `ν` and `d`, bounded by `D`, and carry
  the defining equation `e = ⟨tag, ⟨ν, d⟩⟩`.  The lemmas below show that the two readings
  agree: a block code has at most one decomposition (`isVarsBody_unique`), so the bounded
  quantifiers can only pick the values of the terms, and for `D = (· ∈ W)` with `W` transitive
  the bound is automatic once `e ∈ W`.
-/

section VarsBody

variable {D : ZFSet.{u} → Prop}

/-- Σ side: a `D`-bounded `∃ν ∃d` carrying the defining equation is the matrix evaluated at the
term projections. -/
theorem bddEx_varsBody_iff {e ν d : ZFSet.{u}} {n : ℕ} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (heq : e = ZFSet.pair (natZ n) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    (∃ ν', D ν' ∧ ∃ d', D d' ∧ e = ZFSet.pair (natZ n) (ZFSet.pair ν' d') ∧ P ν' d') ↔ P ν d := by
  constructor
  · rintro ⟨ν', -, d', -, heq', hP⟩
    rw [heq, ZFSet.pair_inj, ZFSet.pair_inj] at heq'
    obtain ⟨-, rfl, rfl⟩ := heq'
    exact hP
  · exact fun hP => ⟨ν, hν, d, hd, heq, hP⟩

/-- Π side: a `D`-bounded `∀ν ∀d` guarded by the defining equation is the matrix evaluated at
the term projections. -/
theorem bddAll_varsBody_iff {e ν d : ZFSet.{u}} {n : ℕ} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (heq : e = ZFSet.pair (natZ n) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    (∀ ν', D ν' → ∀ d', D d' → e = ZFSet.pair (natZ n) (ZFSet.pair ν' d') → P ν' d') ↔ P ν d := by
  constructor
  · exact fun H => H ν hν d hd heq
  · intro hP ν' _ d' _ heq'
    rw [heq, ZFSet.pair_inj, ZFSet.pair_inj] at heq'
    obtain ⟨-, rfl, rfl⟩ := heq'
    exact hP

/-- The term reading itself: quantifying over every decomposition of `e` is the same as
evaluating at the one it has. -/
theorem forall_isVarsBody_iff {e ν d : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (h : IsVarsBody e ν d) :
    (∀ ν' d', IsVarsBody e ν' d' → P ν' d') ↔ P ν d := by
  constructor
  · exact fun H => H ν d h
  · intro hP ν' d' h'
    obtain ⟨rfl, rfl⟩ := isVarsBody_unique h h'
    exact hP

/-- The bounded `∃ν ∃d` of `TrSigP` and the term reading of Definition 13.4 are equivalent. -/
theorem bddEx_iff_forall_isVarsBody {e ν d : ZFSet.{u}} {n : ℕ}
    {P : ZFSet.{u} → ZFSet.{u} → Prop} (hn : n = 1 ∨ n = 2)
    (heq : e = ZFSet.pair (natZ n) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    (∃ ν', D ν' ∧ ∃ d', D d' ∧ e = ZFSet.pair (natZ n) (ZFSet.pair ν' d') ∧ P ν' d') ↔
      ∀ ν' d', IsVarsBody e ν' d' → P ν' d' := by
  have hvb : IsVarsBody e ν d := by
    rcases hn with rfl | rfl
    exacts [Or.inl heq, Or.inr heq]
  rw [bddEx_varsBody_iff heq hν hd, forall_isVarsBody_iff hvb]

/-- The bounded `∀ν ∀d` of `TrPiP` and the term reading of Definition 13.4 are equivalent. -/
theorem bddAll_iff_forall_isVarsBody {e ν d : ZFSet.{u}} {n : ℕ}
    {P : ZFSet.{u} → ZFSet.{u} → Prop} (hn : n = 1 ∨ n = 2)
    (heq : e = ZFSet.pair (natZ n) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    (∀ ν', D ν' → ∀ d', D d' → e = ZFSet.pair (natZ n) (ZFSet.pair ν' d') → P ν' d') ↔
      ∀ ν' d', IsVarsBody e ν' d' → P ν' d' := by
  have hvb : IsVarsBody e ν d := by
    rcases hn with rfl | rfl
    exacts [Or.inl heq, Or.inr heq]
  rw [bddAll_varsBody_iff heq hν hd, forall_isVarsBody_iff hvb]

/-- For `D = (· ∈ W)` with `W` transitive the bound on the two projections is automatic: they
are members of `W` as soon as the code is. -/
theorem mem_of_isVarsBody {W : ZFSet.{u}} (hWt : W.IsTransitive) {e ν d : ZFSet.{u}}
    (h : IsVarsBody e ν d) (he : e ∈ W) : ν ∈ W ∧ d ∈ W := by
  have hp : ZFSet.pair ν d ∈ W := by
    rcases h with rfl | rfl <;> exact snd_mem_of_kpair_mem hWt he
  exact ⟨fst_mem_of_kpair_mem hWt hp, snd_mem_of_kpair_mem hWt hp⟩

/-- The shape actually used in `TrSigP`, where the defining equation sits inside the block
`∃t ∃b` of Definition 13.4. -/
theorem bddEx_varsBody_body_iff {e ν d : ZFSet.{u}} {n : ℕ}
    {Q : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (heq : e = ZFSet.pair (natZ n) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    (∃ ν', D ν' ∧ ∃ d', D d' ∧ ∃ t, D t ∧ ∃ b, D b ∧
        e = ZFSet.pair (natZ n) (ZFSet.pair ν' d') ∧ Q ν' d' t b) ↔
      ∃ t, D t ∧ ∃ b, D b ∧ Q ν d t b := by
  constructor
  · rintro ⟨ν', -, d', -, t, ht, b, hb, heq', hQ⟩
    rw [heq, ZFSet.pair_inj, ZFSet.pair_inj] at heq'
    obtain ⟨-, rfl, rfl⟩ := heq'
    exact ⟨t, ht, b, hb, hQ⟩
  · rintro ⟨t, ht, b, hb, hQ⟩
    exact ⟨ν, hν, d, hd, t, ht, b, hb, heq, hQ⟩

/-- The shape actually used in `TrPiP`, where the defining equation guards the block `∀t ∀b` of
Definition 13.4. -/
theorem bddAll_varsBody_body_iff {e ν d : ZFSet.{u}} {n : ℕ}
    {Q : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (heq : e = ZFSet.pair (natZ n) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    (∀ ν', D ν' → ∀ d', D d' → ∀ t, D t → ∀ b, D b →
        e = ZFSet.pair (natZ n) (ZFSet.pair ν' d') → Q ν' d' t b) ↔
      ∀ t, D t → ∀ b, D b → Q ν d t b := by
  constructor
  · exact fun H t ht b hb => H ν hν d hd t ht b hb heq
  · intro H ν' _ d' _ t ht b hb heq'
    rw [heq, ZFSet.pair_inj, ZFSet.pair_inj] at heq'
    obtain ⟨-, rfl, rfl⟩ := heq'
    exact H t ht b hb

/-- **Definition 13.4** (Σ, `q = 1`) as the paper writes it: with `ν = Vars(e)` and
`d = Body(e)` read as terms, the only quantifiers are `∃t ∃b`. -/
theorem trSigP_one_vars_body {h w e a ν d : ZFSet.{u}}
    (heq : e = ZFSet.pair (natZ 1) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    TrSigP D h w 1 e a ↔ IsSigCodeWD h w 1 e ∧
      ∃ t, D t ∧ ∃ b, D b ∧ IsBlkUpdP w a ν t b ∧ TrMSig D h w d b := by
  rw [trSigP_one]
  exact and_congr_right fun _ => bddEx_varsBody_body_iff heq hν hd

/-- **Definition 13.4** (Π, `q = 1`) as the paper writes it. -/
theorem trPiP_one_vars_body {h w e a ν d : ZFSet.{u}}
    (heq : e = ZFSet.pair (natZ 2) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    TrPiP D h w 1 e a ↔ IsPiCodeWD h w 1 e ∧
      ∀ t, D t → ∀ b, D b → IsBlkUpdP w a ν t b → TrMPi D h w d b := by
  rw [trPiP_one]
  exact and_congr_right fun _ => bddAll_varsBody_body_iff heq hν hd

/-- **Definition 13.4** (Σ, `q + 2`) as the paper writes it. -/
theorem trSigP_add_two_vars_body {h w e a ν d : ZFSet.{u}} {q : ℕ}
    (heq : e = ZFSet.pair (natZ 1) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    TrSigP D h w (q + 2) e a ↔ IsSigCodeWD h w (q + 2) e ∧
      ∃ t, D t ∧ ∃ b, D b ∧ IsBlkUpdP w a ν t b ∧ TrPiP D h w (q + 1) d b := by
  rw [trSigP_add_two]
  exact and_congr_right fun _ => bddEx_varsBody_body_iff heq hν hd

/-- **Definition 13.4** (Π, `q + 2`) as the paper writes it. -/
theorem trPiP_add_two_vars_body {h w e a ν d : ZFSet.{u}} {q : ℕ}
    (heq : e = ZFSet.pair (natZ 2) (ZFSet.pair ν d)) (hν : D ν) (hd : D d) :
    TrPiP D h w (q + 2) e a ↔ IsPiCodeWD h w (q + 2) e ∧
      ∀ t, D t → ∀ b, D b → IsBlkUpdP w a ν t b → TrSigP D h w (q + 1) d b := by
  rw [trPiP_add_two]
  exact and_congr_right fun _ => bddAll_varsBody_body_iff heq hν hd

end VarsBody

/-! ### Complexity (Lemma 13.5, padding form) -/

/-- **Lemma 13.5** for the padding truth predicates: the predicate for `Sig q` codes is `Σ̂q`
(`Σ̂₁` for `q ≤ 1`) and the one for `Pi q` codes is `Π̂q`. -/
theorem trComplexityP : ∀ q : ℕ, ∀ h w e a : ℕ, h ≠ w → h ≠ e → h ≠ a → w ≠ e → w ≠ a → e ≠ a →
    SigmaDef (max q 1) {h, w, e, a} (fun D v => TrSigP.{u} D (v h) (v w) q (v e) (v a)) ∧
    PiDef (max q 1) {h, w, e, a} (fun D v => TrPiP.{u} D (v h) (v w) q (v e) (v a)) := by
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
      have g2 := (delta0_isBlkUpdP.{u} w a m (m + 2) (m + 3) hwa (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).sigma 1
      have g3 := sigmaDef_trMSig.{u} h w (m + 1) (m + 3) hhw (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hmat := g1.and (g2.and g3)
      have s4 := (((hmat.ex (m + 3) le_rfl).ex (m + 2) le_rfl).ex (m + 1) le_rfl).ex m le_rfl
      have gc := (delta0_isSigCodeWD.{u} 1 h w e hhw hhe hwe).sigma 1
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trSigP_one]
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
      have g2 := (delta0_isBlkUpdP.{u} w a m (m + 2) (m + 3) hwa (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).sigma 1
      have g3 := piDef_trMPi.{u} h w (m + 1) (m + 3) hhw (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hmat := g1.imp_pi (g2.imp_pi g3)
      have s4 := (((hmat.all (m + 3) le_rfl).all (m + 2) le_rfl).all (m + 1) le_rfl).all m le_rfl
      have gc := (delta0_isPiCodeWD.{u} 1 h w e hhw hhe hwe).pi 1
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trPiP_one]
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
      have g2 := (delta0_isBlkUpdP.{u} w a m (m + 2) (m + 3) hwa (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).pi (n + 1)
      have hmat := g1.and (g2.and ihP)
      have s4 := (((hmat.ex (m + 3)).ex (m + 2) (by omega)).ex (m + 1) (by omega)).ex m (by omega)
      have gc := (delta0_isSigCodeWD.{u} (n + 2) h w e hhw hhe hwe).sigma (n + 2)
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trSigP_add_two]
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
      have g2 := (delta0_isBlkUpdP.{u} w a m (m + 2) (m + 3) hwa (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).pi (n + 1)
      have hmat := g1.imp_sigma (g2.imp_sigma ihS)
      have s4 := (((hmat.all (m + 3)).all (m + 2) (by omega)).all (m + 1) (by omega)).all m
        (by omega)
      have gc := (delta0_isPiCodeWD.{u} (n + 2) h w e hhw hhe hwe).pi (n + 2)
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trPiP_add_two]
        apply and_congr_right; intro _
        apply forall_congr'; intro ν; apply imp_congr_right; intro _
        apply forall_congr'; intro d; apply imp_congr_right; intro _
        apply forall_congr'; intro t; apply imp_congr_right; intro _
        apply forall_congr'; intro b; apply imp_congr_right; intro _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
        omega

/-! ### Padding block updates inside `W` -/

/-- The value part of a padding block update along `l` has domain `l.length`. -/
theorem isDom_of_blkUpdP {w a t b : ZFSet.{u}} {l : List ℕ}
    (hbu : IsBlkUpdP w a (seqOfNats.{u} l) t b) : IsDom t (natZ.{u} l.length) := by
  intro c
  constructor
  · intro hc
    obtain ⟨j, hj, rfl⟩ := mem_natZ_iff.mp hc
    have hν : ZFSet.pair (natZ.{u} j) (natZ.{u} (l[j]'hj)) ∈ seqOfNats.{u} l :=
      mem_seqOfNats.mpr (List.getElem?_eq_getElem hj)
    exact hbu.2.2.1 _ _ hν
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hbu.2.2.2.1 _ _ hy
    obtain ⟨n, i, hni, he⟩ := mem_seqOfNats_iff.mp hx
    obtain ⟨rfl, -⟩ := ZFSet.pair_injective he
    exact natZ_mem_natZ_iff.mpr (List.getElem?_eq_some_iff.mp hni).1

/-- Any padding block update inside `W` comes from a list of values of `W`.  Unlike
`blkUpd_list` this needs no hypothesis on the domain of `a`. -/
theorem blkUpdP_list {W : ZFSet.{u}} (hWt : W.IsTransitive) (hW : WClosed W)
    {a : ZFSet.{u}} (ha : IsSeqA ωZ W a) {l : List ℕ} (hnd : l.Nodup)
    {t b : ZFSet.{u}} (htW : t ∈ W) (hbu : IsBlkUpdP ωZ a (seqOfNats.{u} l) t b) :
    ∃ xs : List ZFSet.{u}, xs.length = l.length ∧ (∀ x ∈ xs, x ∈ W) ∧
      IsSeqA ωZ W b ∧ SeqVal b = updList (SeqVal a) l xs := by
  have hft : IsFunc t := hbu.2.1
  have hvalt : ∀ i x, ZFSet.pair i x ∈ t → x ∈ W := fun i x hix =>
    snd_mem_of_kpair_mem hWt (hWt.subset_of_mem htW hix)
  have hdt : IsDom t (natZ.{u} l.length) := isDom_of_blkUpdP hbu
  obtain ⟨xs, hlen, hxsW, hteq⟩ : ∃ xs : List ZFSet.{u}, xs.length = l.length ∧
      (∀ x ∈ xs, x ∈ W) ∧ t = seqOfVals xs := by
    refine ⟨(List.range l.length).map (SeqVal.{u} t), by simp, ?_, seq_eq_seqOfVals hft hdt⟩
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact seqVal_mem_of_vals hW.empty_mem hft hvalt k
  rw [hteq] at hbu
  obtain ⟨b₀, hbu₀, hseq₀, hval₀⟩ := exists_blkUpdP hW.empty_mem ha l hnd xs hlen hxsW
  have hbb : b₀ = b := isBlkUpdP_unique hbu₀ hbu
  subst hbb
  exact ⟨xs, hlen, hxsW, hseq₀, hval₀⟩

/-- The padding block update of a sequence of `W` by values of `W` exists inside `W`.  Unlike
`exists_blkUpd_W` this needs no hypothesis on the domain of `a`. -/
theorem exists_blkUpdP_W {W : ZFSet.{u}} (hW : WClosed W) {a : ZFSet.{u}} (ha : IsSeqA ωZ W a)
    {l : List ℕ} (hnd : l.Nodup)
    {xs : List ZFSet.{u}} (hlen : xs.length = l.length) (hxs : ∀ x ∈ xs, x ∈ W) :
    ∃ b, IsBlkUpdP ωZ a (seqOfNats.{u} l) (seqOfVals xs) b ∧ IsSeqA ωZ W b ∧ b ∈ W ∧
      SeqVal b = updList (SeqVal a) l xs := by
  obtain ⟨b, hbu, hseq, hval⟩ := exists_blkUpdP hW.empty_mem ha l hnd xs hlen hxs
  exact ⟨b, hbu, hseq, isSeqA_mem_of_wClosed hW hseq, hval⟩

/-! ### Good assignments for the padding block update -/

/-! ### The quantifier-block step -/

/-! ### Theorem 13.6 for the padding truth predicates -/

end BM4.ST
