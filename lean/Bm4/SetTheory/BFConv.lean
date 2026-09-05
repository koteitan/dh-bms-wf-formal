/-
  Every Σ̂q / Π̂q formula of `Fm` is the underlying formula of a block formula of the same class.
-/
import Bm4.SetTheory.BF

universe u

namespace BM4.ST

open Fm

mutual
theorem exists_bf_sig : ∀ {q : ℕ} {φ : Fm}, IsSigma q φ →
    ∃ b : BF, BF.Sig q b ∧ b.NodupBlocks ∧ b.toFm = φ
  | _, φ, .zero h => ⟨BF.delta true φ, .zero h, trivial, rfl⟩
  | _, _, .succ l hl hnd h => by
    obtain ⟨b, hb, hbnd, hbf⟩ := exists_bf_pi h
    exact ⟨BF.exs l b, .succ hl hb, ⟨hnd, hbnd⟩, by simp [BF.toFm, hbf]⟩
theorem exists_bf_pi : ∀ {q : ℕ} {φ : Fm}, IsPi q φ →
    ∃ b : BF, BF.Pi q b ∧ b.NodupBlocks ∧ b.toFm = φ
  | _, φ, .zero h => ⟨BF.delta true φ, .zero h, trivial, rfl⟩
  | _, _, .succ l hl hnd h => by
    obtain ⟨b, hb, hbnd, hbf⟩ := exists_bf_sig h
    exact ⟨BF.alls l b, .succ hl hb, ⟨hnd, hbnd⟩, by simp [BF.toFm, hbf]⟩
end

end BM4.ST
