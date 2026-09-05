/-
  The characterisation of the ancestor relation of the expanded array, derived from the
  paper's own six claims (Theorem 6.3, assembled in `Bm4/CopyPaper/Assemble.lean`).

  `Bm4/Copy.lean` fixes the two shapes `ParForm` and `AncForm` in which the parent and
  ancestor relations of `G ⌢ B₀ ⌢ B₁ ⌢ ⋯` are described.  This file proves

  * `anc_tA_iff`     — `y ≺ₖ D_j⁽ᑫ⁾` in the expanded array is exactly `AncForm`;
  * `anc_tA_cases`   — the coarse position information contained in it;
  * `hasParent_tA_of_parForm` — a column described by `ParForm` really has a `k`-parent.

  Everything is obtained from the claims `Claim1`–`Claim6` of `Bm4/CopyPaper/Interval.lean`
  through `stage1`, `stage3` and `claim4`, together with `passing`, `lead_bridge`
  (`Bm4/CopyPaper/L6.lean`) and `anc_lead_of_anc_lead` (`Bm4/CopyPaper/L4.lean`).
  No closed-form shortcut is used anywhere below.

  The three disjuncts of `AncForm k y q j` correspond to the three ways a `k`-ancestor of
  `D_j⁽ᑫ⁾` can be placed:

  1. inside the same copy `Bq`, mirroring `D_i ≺ᴬₖ D_j`;
  2. inside a strictly earlier copy `Ba`, which by the passing property forces the chain
     through every intermediate leading column — possible only for `k < m₀`, and then
     equivalent to `D_i ≺ᴬₖ C` together with `P ≼ᴬₖ D_j`;
  3. inside the common prefix `G`, mirroring `y ≺ᴬₖ D_j`.
-/
import Bm4.CopyPaper.Assemble

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

namespace BadRoot

variable (b : BadRoot A)

/-! ### Iterating the bridge between leading columns -/

/-- For `k < m₀` the bridge `P⁽ᶜ⁾ ≺ₖ P⁽ᶜ⁺¹⁾` of `lead_bridge` iterates: any leading column is a
non-strict `k`-ancestor of every later leading column. -/
private theorem lead_run {k : ℕ} (hk : k < b.m) (h3 : b.Claim3 k) (c₁ : ℕ) :
    ∀ c₂, c₁ ≤ c₂ → ancEq b.tA k (b.pos c₁ 0) (b.pos c₂ 0) := by
  intro c₂
  induction c₂ with
  | zero =>
    intro h
    have : c₁ = 0 := Nat.le_zero.mp h
    subst this
    exact ancEq_refl _ _ _
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge n c₁ with hlt | hge
    · have hc : c₁ = n + 1 := by omega
      subst hc
      exact ancEq_refl _ _ _
    · exact ancEq_trans (ih hge) (Or.inr (b.lead_bridge hk h3 n))

/-! ### The characterisation -/

/-- The `k`-ancestors of `D_j⁽ᑫ⁾` in the expanded array, in the shape `AncForm`.

*Forward.*  An ancestor `y` is either in `G` — then `Claim2 k` transports it — or `y = D_i⁽ᵃ⁾`
with `a ≤ q`.  For `a = q` this is `Claim1 k`.  For `a < q` the passing property splits the
chain at the leading column `P⁽ᑫ⁾`; `Claim4` would put `y` in `G`, so `k < m₀`; then
`anc_lead_of_anc_lead` walks the target down to `P⁽ᵃ⁺¹⁾` and `Claim3 k` transports the head to
`D_i ≺ᴬₖ C`, while `Claim1 k` turns the tail into `P ≼ᴬₖ D_j`.

*Backward.*  `Claim1 k` and `Claim2 k` handle the first and third disjuncts.  For the second,
`Claim3 k` produces `D_i⁽ᵃ⁾ ≺ₖ P⁽ᵃ⁺¹⁾`, `lead_run` continues to `P⁽ᑫ⁾`, and `Claim1 k` appends
the copy-internal tail. -/
theorem anc_tA_iff (k : ℕ) {q j : ℕ} (hj : j < b.s) (y : ℕ) :
    anc b.tA k y (b.pos q j) ↔ b.AncForm k y q j := by
  have hst := b.stage3 k
  have hc1 : b.Claim1 k := hst.1
  have hc5 : b.Claim5 k := hst.2.1
  have hc2 : b.Claim2 k := hst.2.2.1
  have hc6 : b.Claim6 k := hst.2.2.2
  unfold AncForm
  constructor
  · intro h
    rcases lt_or_ge y b.p with hy | hy
    · -- the ancestor lives in the common prefix
      exact Or.inr (Or.inr ⟨hy, (hc2 q j y hj hy).mp h⟩)
    · obtain ⟨a, i, hi, rfl⟩ := b.exists_pos hy
      have haq : a ≤ q := by
        by_contra hcon
        have hgt : b.pos q j < b.pos a i := b.pos_lt_pos_of_lt (by omega) hj
        have := anc_lt h
        omega
      rcases eq_or_lt_of_le haq with heq | hlt
      · -- same copy
        subst heq
        exact Or.inl ⟨i, rfl, (hc1 _ i j hi hj).mp h⟩
      · -- a strictly earlier copy
        obtain ⟨hA, hT⟩ := b.passing hc1 hc5 hlt hi hj h
        have hkm : k < b.m := by
          by_contra hcon
          have hlow := b.claim4 k (not_lt.mp hcon) q (b.pos a i) (by omega) hA
          have := b.p_le_pos a i
          omega
        have hc3 : b.Claim3 k := (b.stage1 k hkm).2.1
        have hstep : anc b.tA k (b.pos a i) (b.pos (a + 1) 0) :=
          b.anc_lead_of_anc_lead hc6 hi q hlt hA
        have hbr := hc3 (a + 1) i (Nat.succ_pos a) hi
        simp only [Nat.add_sub_cancel] at hbr
        have hAA : anc A k (b.p + i) (A.len - 1) := hbr.mp hstep
        have hEq : ancEq A k b.p (b.p + j) := by
          rcases hT with hteq | htanc
          · have h0 : (0 : ℕ) = j := (b.pos_inj b.s_pos hj hteq).2
            exact Or.inl (by omega)
          · exact Or.inr (by simpa using (hc1 q 0 j b.s_pos hj).mp htanc)
        exact Or.inr (Or.inl ⟨hkm, hEq, a, hlt, i, rfl, hAA⟩)
  · intro h
    rcases h with ⟨i, rfl, hA⟩ | ⟨hkm, hEq, a, hlt, i, rfl, hAA⟩ | ⟨hy, hA⟩
    · have hij : i < j := by have := anc_lt hA; omega
      exact (hc1 q i j (hij.trans hj) hj).mpr hA
    · have hi : i < b.s := b.lt_s_of_lt_c (anc_lt hAA)
      have hc3 : b.Claim3 k := (b.stage1 k hkm).2.1
      have hbr := hc3 (a + 1) i (Nat.succ_pos a) hi
      simp only [Nat.add_sub_cancel] at hbr
      have hstep : anc b.tA k (b.pos a i) (b.pos (a + 1) 0) := hbr.mpr hAA
      have hrun : ancEq b.tA k (b.pos (a + 1) 0) (b.pos q 0) :=
        b.lead_run hkm hc3 (a + 1) q (by omega)
      have hlead : anc b.tA k (b.pos a i) (b.pos q 0) := by
        rcases hrun with hreq | hranc
        · rw [← hreq]; exact hstep
        · exact anc_trans hstep hranc
      rcases hEq with hteq | htanc
      · have hj0 : j = 0 := by omega
        subst hj0
        exact hlead
      · have htail : anc b.tA k (b.pos q 0) (b.pos q j) :=
          (hc1 q 0 j b.s_pos hj).mpr (by simpa using htanc)
        exact anc_trans hlead htail
    · exact (hc2 q j y hj hy).mpr hA

/-- The position information carried by `anc_tA_iff`: a `k`-ancestor of `D_j⁽ᑫ⁾` lies in the
common prefix, in a strictly earlier copy, or strictly earlier in the same copy. -/
theorem anc_tA_cases (k : ℕ) {q j y : ℕ} (hj : j < b.s) (h : anc b.tA k y (b.pos q j)) :
    y < b.p ∨ (∃ a < q, ∃ i < b.s, y = b.pos a i) ∨ ∃ i < j, y = b.pos q i := by
  have hf := (b.anc_tA_iff k hj y).mp h
  unfold AncForm at hf
  rcases hf with ⟨i, rfl, hA⟩ | ⟨-, -, a, hlt, i, rfl, hAA⟩ | ⟨hy, -⟩
  · exact Or.inr (Or.inr ⟨i, by have := anc_lt hA; omega, rfl⟩)
  · exact Or.inr (Or.inl ⟨a, hlt, i, b.lt_s_of_lt_c (anc_lt hAA), rfl⟩)
  · exact Or.inl hy

/-- A column described by `ParForm` really has a `k`-parent in the expanded array.

Each of the three branches turns its `A`-parent into an `A`-ancestor, feeds the corresponding
disjunct of `AncForm` to `anc_tA_iff`, and reads off the last step of the resulting chain.
The side condition of the third branch is not needed for this weaker conclusion. -/
theorem hasParent_tA_of_parForm (k : ℕ) {q j y : ℕ} (hj : j < b.s) (h : b.ParForm k y q j) :
    HasParent b.tA k (b.pos q j) := by
  have hanc : ∃ z, anc b.tA k z (b.pos q j) := by
    unfold ParForm at h
    rcases h with ⟨i, rfl, hp⟩ | ⟨hj0, hq, hkm, i, rfl, hp⟩ | ⟨-, hy, hp⟩
    · exact ⟨b.pos q i, (b.anc_tA_iff k hj _).mpr (Or.inl ⟨i, rfl, anc_of_parent hp⟩)⟩
    · refine ⟨b.pos (q - 1) i, (b.anc_tA_iff k hj _).mpr (Or.inr (Or.inl
        ⟨hkm, Or.inl (by omega), q - 1, by omega, i, rfl, anc_of_parent hp⟩))⟩
    · exact ⟨y, (b.anc_tA_iff k hj _).mpr (Or.inr (Or.inr ⟨hy, anc_of_parent hp⟩))⟩
  obtain ⟨z, hz⟩ := hanc
  obtain ⟨u, -, hu⟩ := anc_last_step hz
  exact ⟨u, hu⟩

end BadRoot

end BM4
