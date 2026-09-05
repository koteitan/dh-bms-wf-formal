/-
  Part III, §12: padding of block formulas (Lemma 12.2 (3)).

  The paper's padding moves a Σ̂j formula to an equivalent Σ̂q formula for `j ≤ q` by "adding as
  many vacuous blocks as needed at the innermost position, quantifying a variable that does not
  occur in the formula".  `Bm4/SetTheory/Fm.lean` has that on the inductive type `Fm`
  (`IsSigma.pad`), but Lemma 12.2 (3) is a statement about *codes*, and the codes of the
  development are the block codes `BF.code`.  This file supplies the missing middle layer: the
  padding operation on `BF` itself, together with the three facts the lemma asserts — the class
  goes up by one, Definition 12.1's block condition survives, and the result is equivalent over
  every nonempty domain.

  As in the paper, nonemptiness is used for nothing but choosing a value for the vacuous variable
  (`Fm.sat_ex_of_notMem`); no transitivity, no other hypothesis on the domain.
-/
import Bm4.SetTheory.BF

universe u

namespace BM4.ST
namespace BF

/-! ### One vacuous block at the innermost position -/

mutual
/-- Add one vacuous block at the innermost position of a Σ̂-shaped block formula. -/
def padSig : BF → BF
  | delta sg φ => exs [Fm.fresh (Fm.fv φ)] (delta sg φ)
  | exs l ψ => exs l (padPi ψ)
  | alls l ψ => alls l ψ
/-- The Π̂-shaped counterpart. -/
def padPi : BF → BF
  | delta sg φ => alls [Fm.fresh (Fm.fv φ)] (delta sg φ)
  | alls l ψ => alls l (padSig ψ)
  | exs l ψ => exs l ψ
end

@[simp] theorem padSig_delta (sg : Bool) (φ : Fm) :
    padSig (delta sg φ) = exs [Fm.fresh (Fm.fv φ)] (delta sg φ) := rfl
@[simp] theorem padSig_exs (l : List ℕ) (ψ : BF) : padSig (exs l ψ) = exs l (padPi ψ) := rfl
@[simp] theorem padPi_delta (sg : Bool) (φ : Fm) :
    padPi (delta sg φ) = alls [Fm.fresh (Fm.fv φ)] (delta sg φ) := rfl
@[simp] theorem padPi_alls (l : List ℕ) (ψ : BF) : padPi (alls l ψ) = alls l (padSig ψ) := rfl

theorem fv_toFm_delta (sg : Bool) (φ : Fm) : Fm.fv (toFm (delta sg φ)) = Fm.fv φ := by
  cases sg <;> simp [toFm]

theorem fresh_notMem_toFm_delta (sg : Bool) (φ : Fm) :
    Fm.fresh (Fm.fv φ) ∉ Fm.fv (toFm (delta sg φ)) := by
  rw [fv_toFm_delta]; exact Fm.fresh_notMem _

/-! ### The class goes up by one -/

mutual
theorem Sig.padSig : ∀ {q : ℕ} {b : BF}, Sig q b → Sig (q + 1) (BF.padSig b)
  | _, _, .zero h => .succ (by simp) (.zero h)
  | _, _, .succ hl h => .succ hl (Pi.padPi h)
theorem Pi.padPi : ∀ {q : ℕ} {b : BF}, Pi q b → Pi (q + 1) (BF.padPi b)
  | _, _, .zero h => .succ (by simp) (.zero h)
  | _, _, .succ hl h => .succ hl (Sig.padSig h)
end

/-! ### Definition 12.1's block condition survives -/

mutual
theorem nodupBlocks_padSig : ∀ b : BF, NodupBlocks b → NodupBlocks (padSig b)
  | delta sg φ, _ => ⟨by simp, trivial⟩
  | exs l ψ, h => ⟨h.1, nodupBlocks_padPi ψ h.2⟩
  | alls l ψ, h => h
theorem nodupBlocks_padPi : ∀ b : BF, NodupBlocks b → NodupBlocks (padPi b)
  | delta sg φ, _ => ⟨by simp, trivial⟩
  | alls l ψ, h => ⟨h.1, nodupBlocks_padSig ψ h.2⟩
  | exs l ψ, h => h
end

/-! ### Same free variables, same meaning over a nonempty domain -/

mutual
theorem fv_padSig : ∀ b : BF, Fm.fv (padSig b).toFm = Fm.fv b.toFm
  | delta sg φ => by
    show Fm.fv (Fm.exs [Fm.fresh (Fm.fv φ)] (toFm (delta sg φ))) = _
    rw [Fm.fv_exs]
    have hz := fresh_notMem_toFm_delta sg φ
    ext x
    simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_singleton]
    exact ⟨And.left, fun hx => ⟨hx, fun he => hz (he ▸ hx)⟩⟩
  | exs l ψ => by
    show Fm.fv (Fm.exs l (padPi ψ).toFm) = Fm.fv (Fm.exs l ψ.toFm)
    rw [Fm.fv_exs, Fm.fv_exs, fv_padPi ψ]
  | alls l ψ => rfl
theorem fv_padPi : ∀ b : BF, Fm.fv (padPi b).toFm = Fm.fv b.toFm
  | delta sg φ => by
    show Fm.fv (Fm.alls [Fm.fresh (Fm.fv φ)] (toFm (delta sg φ))) = _
    rw [Fm.fv_alls]
    have hz := fresh_notMem_toFm_delta sg φ
    ext x
    simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_singleton]
    exact ⟨And.left, fun hx => ⟨hx, fun he => hz (he ▸ hx)⟩⟩
  | alls l ψ => by
    show Fm.fv (Fm.alls l (padSig ψ).toFm) = Fm.fv (Fm.alls l ψ.toFm)
    rw [Fm.fv_alls, Fm.fv_alls, fv_padSig ψ]
  | exs l ψ => rfl
end

mutual
theorem sat_padSig : ∀ (b : BF) (D : ZFSet.{u} → Prop), (∃ x, D x) →
    ∀ v : ℕ → ZFSet.{u}, (Fm.Sat D v (padSig b).toFm ↔ Fm.Sat D v b.toFm)
  | delta sg φ, D, hD, v => by
    show Fm.Sat D v (Fm.exs [Fm.fresh (Fm.fv φ)] (toFm (delta sg φ))) ↔ _
    exact Fm.sat_ex_of_notMem (fresh_notMem_toFm_delta sg φ) hD
  | exs l ψ, D, hD, v => by
    show Fm.Sat D v (Fm.exs l (padPi ψ).toFm) ↔ Fm.Sat D v (Fm.exs l ψ.toFm)
    exact Fm.sat_exs_congr (sat_padPi ψ D hD) l v
  | alls l ψ, D, _, v => Iff.rfl
theorem sat_padPi : ∀ (b : BF) (D : ZFSet.{u} → Prop), (∃ x, D x) →
    ∀ v : ℕ → ZFSet.{u}, (Fm.Sat D v (padPi b).toFm ↔ Fm.Sat D v b.toFm)
  | delta sg φ, D, hD, v => by
    show Fm.Sat D v (Fm.alls [Fm.fresh (Fm.fv φ)] (toFm (delta sg φ))) ↔ _
    exact Fm.sat_all_of_notMem (fresh_notMem_toFm_delta sg φ) hD
  | alls l ψ, D, hD, v => by
    show Fm.Sat D v (Fm.alls l (padSig ψ).toFm) ↔ Fm.Sat D v (Fm.alls l ψ.toFm)
    exact Fm.sat_alls_congr (sat_padSig ψ D hD) l v
  | exs l ψ, D, _, v => Iff.rfl
end

/-! ### Padding by several levels (Lemma 12.2 (3)) -/

/-- Add `n` vacuous blocks at the innermost position. -/
def padSigN : BF → ℕ → BF
  | b, 0 => b
  | b, n + 1 => padSigN (padSig b) n

/-- The Π̂-shaped counterpart. -/
def padPiN : BF → ℕ → BF
  | b, 0 => b
  | b, n + 1 => padPiN (padPi b) n

@[simp] theorem padSigN_zero (b : BF) : padSigN b 0 = b := rfl
@[simp] theorem padPiN_zero (b : BF) : padPiN b 0 = b := rfl
theorem padSigN_succ (b : BF) (n : ℕ) : padSigN b (n + 1) = padSigN (padSig b) n := rfl
theorem padPiN_succ (b : BF) (n : ℕ) : padPiN b (n + 1) = padPiN (padPi b) n := rfl

theorem Sig.padSigN : ∀ (n : ℕ) {q : ℕ} {b : BF}, Sig q b → Sig (q + n) (BF.padSigN b n)
  | 0, _, _, h => h
  | n + 1, q, b, h => by
    have := Sig.padSigN n h.padSig
    show Sig (q + (n + 1)) (BF.padSigN (BF.padSig b) n)
    exact (by omega : q + 1 + n = q + (n + 1)) ▸ this

theorem Pi.padPiN : ∀ (n : ℕ) {q : ℕ} {b : BF}, Pi q b → Pi (q + n) (BF.padPiN b n)
  | 0, _, _, h => h
  | n + 1, q, b, h => by
    have := Pi.padPiN n h.padPi
    show Pi (q + (n + 1)) (BF.padPiN (BF.padPi b) n)
    exact (by omega : q + 1 + n = q + (n + 1)) ▸ this

theorem nodupBlocks_padSigN : ∀ (n : ℕ) (b : BF), NodupBlocks b → NodupBlocks (padSigN b n)
  | 0, _, h => h
  | n + 1, b, h => nodupBlocks_padSigN n _ (nodupBlocks_padSig b h)

theorem nodupBlocks_padPiN : ∀ (n : ℕ) (b : BF), NodupBlocks b → NodupBlocks (padPiN b n)
  | 0, _, h => h
  | n + 1, b, h => nodupBlocks_padPiN n _ (nodupBlocks_padPi b h)

theorem fv_padSigN : ∀ (n : ℕ) (b : BF), Fm.fv (padSigN b n).toFm = Fm.fv b.toFm
  | 0, _ => rfl
  | n + 1, b => by rw [padSigN_succ, fv_padSigN n, fv_padSig]

theorem fv_padPiN : ∀ (n : ℕ) (b : BF), Fm.fv (padPiN b n).toFm = Fm.fv b.toFm
  | 0, _ => rfl
  | n + 1, b => by rw [padPiN_succ, fv_padPiN n, fv_padPi]

theorem sat_padSigN : ∀ (n : ℕ) (b : BF) (D : ZFSet.{u} → Prop), (∃ x, D x) →
    ∀ v : ℕ → ZFSet.{u}, (Fm.Sat D v (padSigN b n).toFm ↔ Fm.Sat D v b.toFm)
  | 0, _, _, _, _ => Iff.rfl
  | n + 1, b, D, hD, v => by
    rw [padSigN_succ]
    exact (sat_padSigN n _ D hD v).trans (sat_padSig b D hD v)

theorem sat_padPiN : ∀ (n : ℕ) (b : BF) (D : ZFSet.{u} → Prop), (∃ x, D x) →
    ∀ v : ℕ → ZFSet.{u}, (Fm.Sat D v (padPiN b n).toFm ↔ Fm.Sat D v b.toFm)
  | 0, _, _, _, _ => Iff.rfl
  | n + 1, b, D, hD, v => by
    rw [padPiN_succ]
    exact (sat_padPiN n _ D hD v).trans (sat_padPi b D hD v)

theorem padSigN_exs : ∀ (n : ℕ) (l : List ℕ) (ψ : BF),
    padSigN (exs l ψ) n = exs l (padPiN ψ n)
  | 0, _, _ => rfl
  | n + 1, l, ψ => by
    rw [padSigN_succ, padSig_exs, padSigN_exs n, padPiN_succ]

theorem padPiN_alls : ∀ (n : ℕ) (l : List ℕ) (ψ : BF),
    padPiN (alls l ψ) n = alls l (padSigN ψ n)
  | 0, _, _ => rfl
  | n + 1, l, ψ => by
    rw [padPiN_succ, padPi_alls, padPiN_alls n, padSigN_succ]

/-! ### The explicit shape of a padded Δ₀ block formula

Since the matrix never changes along the padding, every vacuous block quantifies the *same*
variable `z = fresh (fv φ)`.  `vacSig` / `vacPi` name that shape; it is what the code-level
recognizer of `Bm4/SetTheory/SynPad.lean` matches against. -/

mutual
/-- `b` wrapped in `n` alternating vacuous blocks on `z`, outermost `∃`. -/
def vacSig (z : ℕ) : ℕ → BF → BF
  | 0, b => b
  | n + 1, b => exs [z] (vacPi z n b)
/-- `b` wrapped in `n` alternating vacuous blocks on `z`, outermost `∀`. -/
def vacPi (z : ℕ) : ℕ → BF → BF
  | 0, b => b
  | n + 1, b => alls [z] (vacSig z n b)
end

@[simp] theorem vacSig_zero (z : ℕ) (b : BF) : vacSig z 0 b = b := rfl
@[simp] theorem vacPi_zero (z : ℕ) (b : BF) : vacPi z 0 b = b := rfl
theorem vacSig_succ (z n : ℕ) (b : BF) : vacSig z (n + 1) b = exs [z] (vacPi z n b) := rfl
theorem vacPi_succ (z n : ℕ) (b : BF) : vacPi z (n + 1) b = alls [z] (vacSig z n b) := rfl

mutual
theorem padSig_vacSig (sg : Bool) (φ : Fm) :
    ∀ n : ℕ, padSig (vacSig (Fm.fresh (Fm.fv φ)) n (delta sg φ)) =
      vacSig (Fm.fresh (Fm.fv φ)) (n + 1) (delta sg φ)
  | 0 => rfl
  | n + 1 => by
    rw [vacSig_succ, padSig_exs, padPi_vacPi sg φ n, vacSig_succ]
theorem padPi_vacPi (sg : Bool) (φ : Fm) :
    ∀ n : ℕ, padPi (vacPi (Fm.fresh (Fm.fv φ)) n (delta sg φ)) =
      vacPi (Fm.fresh (Fm.fv φ)) (n + 1) (delta sg φ)
  | 0 => rfl
  | n + 1 => by
    rw [vacPi_succ, padPi_alls, padSig_vacSig sg φ n, vacPi_succ]
end

theorem padSigN_vacSig (sg : Bool) (φ : Fm) :
    ∀ (n k : ℕ), padSigN (vacSig (Fm.fresh (Fm.fv φ)) k (delta sg φ)) n =
      vacSig (Fm.fresh (Fm.fv φ)) (k + n) (delta sg φ)
  | 0, k => by simp
  | n + 1, k => by
    rw [padSigN_succ, padSig_vacSig sg φ k, padSigN_vacSig sg φ n (k + 1),
      show k + 1 + n = k + (n + 1) by omega]

theorem padPiN_vacPi (sg : Bool) (φ : Fm) :
    ∀ (n k : ℕ), padPiN (vacPi (Fm.fresh (Fm.fv φ)) k (delta sg φ)) n =
      vacPi (Fm.fresh (Fm.fv φ)) (k + n) (delta sg φ)
  | 0, k => by simp
  | n + 1, k => by
    rw [padPiN_succ, padPi_vacPi sg φ k, padPiN_vacPi sg φ n (k + 1),
      show k + 1 + n = k + (n + 1) by omega]

/-- Padding a Δ₀ block formula `n` times is exactly `n` vacuous blocks on the fresh variable. -/
theorem padSigN_delta (n : ℕ) (sg : Bool) (φ : Fm) :
    padSigN (delta sg φ) n = vacSig (Fm.fresh (Fm.fv φ)) n (delta sg φ) := by
  have := padSigN_vacSig sg φ n 0
  simpa using this

theorem padPiN_delta (n : ℕ) (sg : Bool) (φ : Fm) :
    padPiN (delta sg φ) n = vacPi (Fm.fresh (Fm.fv φ)) n (delta sg φ) := by
  have := padPiN_vacPi sg φ n 0
  simpa using this

/-- **Lemma 12.2 (3)** at the block-formula layer: for `j ≤ q`, every Σ̂j block formula moves to a
Σ̂q block formula with the same free variables, equivalent to it in every nonempty domain. -/
theorem Sig.pad {j q : ℕ} (hjq : j ≤ q) {b : BF} (h : Sig j b) (hnd : NodupBlocks b) :
    ∃ b' : BF, Sig q b' ∧ NodupBlocks b' ∧ Fm.fv b'.toFm = Fm.fv b.toFm ∧
      ∀ (D : ZFSet.{u} → Prop), (∃ x, D x) →
        ∀ v : ℕ → ZFSet.{u}, (Fm.Sat D v b'.toFm ↔ Fm.Sat D v b.toFm) := by
  refine ⟨BF.padSigN b (q - j), ?_, nodupBlocks_padSigN _ b hnd, fv_padSigN _ b,
    fun D hD v => sat_padSigN _ b D hD v⟩
  have := Sig.padSigN (q - j) h
  rwa [show j + (q - j) = q by omega] at this

/-- Lemma 12.2 (3) for Π̂. -/
theorem Pi.pad {j q : ℕ} (hjq : j ≤ q) {b : BF} (h : Pi j b) (hnd : NodupBlocks b) :
    ∃ b' : BF, Pi q b' ∧ NodupBlocks b' ∧ Fm.fv b'.toFm = Fm.fv b.toFm ∧
      ∀ (D : ZFSet.{u} → Prop), (∃ x, D x) →
        ∀ v : ℕ → ZFSet.{u}, (Fm.Sat D v b'.toFm ↔ Fm.Sat D v b.toFm) := by
  refine ⟨BF.padPiN b (q - j), ?_, nodupBlocks_padPiN _ b hnd, fv_padPiN _ b,
    fun D hD v => sat_padPiN _ b D hD v⟩
  have := Pi.padPiN (q - j) h
  rwa [show j + (q - j) = q by omega] at this

end BF
end BM4.ST
