/-
  The standardness invariant (Proposition 7.1) and agreement of Definition 5.1 with the
  published BM4 rule on reachable arrays (Remark 7.2).
-/
import Bm4.Expand

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

/-- Having a `k`-parent forces a positive `k`-entry (the easy direction of (7.1)). -/
theorem hasParent_pos {k i : ℕ} (h : HasParent A k i) : 0 < A.col i k := by
  obtain ⟨y, hy⟩ := h
  exact lt_of_le_of_lt (Nat.zero_le _) (parent_val_lt hy)

theorem hasParent_congr {B : Arr r} {k i : ℕ}
    (hag : ∀ x ≤ i, ∀ k', A.col x k' = B.col x k') (hA : i < A.len) (hB : i < B.len) :
    HasParent A k i ↔ HasParent B k i :=
  exists_congr fun y => parent_congr_iff hag hA hB y

/-- In `E r`, column `0` is the `k`-parent of column `1` for every row `k < r`. -/
theorem parent_E_zero_one (r : ℕ) : ∀ k < r, parent (E r) k 0 1 := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact ⟨Nat.zero_lt_one, Nat.zero_lt_one, by simp [E], fun j' h1 h2 _ => by omega, hk,
      by simp [E]⟩
  | succ k ih =>
    intro hk
    exact ⟨Nat.zero_lt_one, anc_of_parent (ih (by omega)), by simp [E],
      fun j' h1 h2 _ => by omega, hk, by simp [E]⟩

/-- **Proposition 7.1** (standardness invariant): in every array reachable from `E r`, an entry
is positive iff the column has a parent in that row. -/
theorem standard_invariant (hA : Reachable r A) :
    ∀ i < A.len, ∀ k < r, (0 < A.col i k ↔ HasParent A k i) := by
  suffices H : ∀ i < A.len, ∀ k < r, 0 < A.col i k → HasParent A k i by
    intro i hi k hk
    exact ⟨H i hi k hk, hasParent_pos⟩
  induction hA with
  | init =>
    intro i hi k hk hpos
    have hi2 : i < 2 := hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · exact absurd hpos (by simp [E])
    · exact ⟨0, parent_E_zero_one r k hk⟩
  | @step A N hA ih =>
    intro i hi k hk hpos
    by_cases h0 : A.len = 0
    · rw [expand_of_len_zero h0] at hi hpos ⊢
      exact ih i hi k hk hpos
    by_cases h : LastHasParent A
    · -- `A[N]` **is** the array `Ã` of Definition 5.1, so no transport is needed
      set b := toBadRoot h N with hb
      rw [expand_eq h N] at hi hpos ⊢
      rcases lt_or_ge i b.p with hip | hip
      · have hiA : i < A.len := by have := b.p_lt_c; omega
        rw [b.col_lt hip] at hpos
        have := ih i hiA k hk hpos
        exact (hasParent_congr (A := A) (B := b.tA)
          (fun x hx k' => (b.col_lt (lt_of_le_of_lt hx hip)).symm) hiA hi).mp this
      · obtain ⟨q, j, hj, rfl⟩ := b.exists_pos hip
        have hqN : q ≤ b.N := b.le_N_of_pos_lt_tA_len hi
        rw [b.col_pos hj] at hpos
        by_cases hasc : b.Asc k j
        · rw [if_pos hasc] at hpos
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · rcases Nat.eq_zero_or_pos q with rfl | hq
            · -- `P` itself: its parent in `A` transports by (C2)
              simp only [Nat.add_zero, zero_mul] at hpos
              have hpA : b.p < A.len := by have := b.p_lt_c; omega
              exact b.hasParent_tA_of_hasParent_A k hqN hj
                (by simpa using ih b.p hpA k hk hpos)
            · -- a later leading column `P⁽ᑫ⁾`: (C3) brings the parent of `C` across
              exact b.hasParent_tA_lead hasc.1 hqN hq
          · -- an ascending column with `j > 0`: `P ≺ᴬₖ D_j`, so `D_j` has a `k`-parent in `A`
            have hanc : anc A k b.p (b.p + j) := anc_of_ancEq_of_ne hasc.2 (by omega)
            exact b.hasParent_tA_of_hasParent_A k hqN hj
              (exists_parent_of_valid hk (by have := b.lt_c_of_lt_s hj; omega)
                (cand_of_anc hanc) (anc_val_lt hanc))
        · -- a non-ascending column keeps its entry, so the induction hypothesis applies to `D_j`
          rw [if_neg hasc] at hpos
          have hpjA : b.p + j < A.len := by have := b.lt_c_of_lt_s hj; omega
          exact b.hasParent_tA_of_hasParent_A k hqN hj (ih (b.p + j) hpjA k hk hpos)
    · rw [expand_of_not_lastHasParent h0 h] at hi hpos ⊢
      have hi' : i < A.len := by
        have : i < A.len - 1 := hi
        omega
      have hpos' : 0 < A.col i k := hpos
      have := ih i hi' k hk hpos'
      exact (hasParent_congr (A := A) (B := dropLast A) (fun _ _ _ => rfl) hi' hi).mp this

/-! ### Corollaries (7.2) and (7.3) -/

/-- Any parent in some row gives a `0`-parent. -/
theorem hasParent_zero_of_hasParent {k i : ℕ} (h : HasParent A k i) : HasParent A 0 i := by
  obtain ⟨y, hy⟩ := h
  have h0 : anc A 0 y i := anc_mono (Nat.zero_le k) (anc_of_parent hy)
  obtain ⟨b', _, hb'⟩ := anc_last_step h0
  exact ⟨b', hb'⟩

/-- (7.2), first equivalence: the last column has a zero in row `0` iff it has no parent. -/
theorem last_zero_iff (hr : 0 < r) (hA : Reachable r A) (h0 : 0 < A.len) :
    A.col (A.len - 1) 0 = 0 ↔ ¬ LastHasParent A := by
  constructor
  · intro hz ⟨_, k, _, hk⟩
    have := hasParent_pos (hasParent_zero_of_hasParent hk)
    omega
  · intro hn
    have hno : ¬ HasParent A 0 (A.len - 1) := fun hp => hn ⟨h0, 0, hr, hp⟩
    have := (standard_invariant hA (A.len - 1) (by omega) 0 hr)
    have : ¬ 0 < A.col (A.len - 1) 0 := fun hpos => hno (this.mp hpos)
    omega

/-- (7.2), second equivalence: the last column is the zero column iff it has no parent. -/
theorem last_all_zero_iff (hr : 0 < r) (hA : Reachable r A) (h0 : 0 < A.len) :
    (∀ k < r, A.col (A.len - 1) k = 0) ↔ ¬ LastHasParent A := by
  constructor
  · intro hz
    exact (last_zero_iff hr hA h0).mp (hz 0 hr)
  · intro hn k hk
    have hno : ¬ HasParent A k (A.len - 1) := fun hp => hn ⟨h0, k, hk, hp⟩
    have := (standard_invariant hA (A.len - 1) (by omega) k hk)
    have : ¬ 0 < A.col (A.len - 1) k := fun hpos => hno (this.mp hpos)
    omega

/-- (7.3): the maximal parent row of the last column is the maximal row with a positive entry. -/
theorem m₀_eq_findGreatest_pos (hr : 0 < r) (hA : Reachable r A) (h : LastHasParent A) :
    m₀ A = Nat.findGreatest (fun k => 0 < A.col (A.len - 1) k) (r - 1) := by
  have hm₀r : m₀ A < r := m₀_lt hr
  have hm₀le : m₀ A ≤ r - 1 := by omega
  have hpos : 0 < A.col (A.len - 1) (m₀ A) := hasParent_pos (m₀_hasParent h)
  apply le_antisymm
  · exact Nat.le_findGreatest hm₀le hpos
  · have hg : 0 < A.col (A.len - 1) (Nat.findGreatest (fun k => 0 < A.col (A.len - 1) k) (r - 1)) :=
      Nat.findGreatest_spec (P := fun k => 0 < A.col (A.len - 1) k) hm₀le hpos
    have hgle : Nat.findGreatest (fun k => 0 < A.col (A.len - 1) k) (r - 1) ≤ r - 1 :=
      Nat.findGreatest_le _
    have hgr : Nat.findGreatest (fun k => 0 < A.col (A.len - 1) k) (r - 1) < r := by omega
    have hpar := (standard_invariant hA (A.len - 1) (by have := h.1; omega) _ hgr).mp hg
    exact le_m₀ hgr hpar

/-! ### The published rule (Remark 7.2) -/

/-- The published BM4 rule [1,2]: delete the last column if its row-0 entry is 0; otherwise take
the largest row `m` with a positive entry in the last column, the `m`-parent `p` of the last
column, and copy the bad part `(A_p, …, A_{c-1})` `N+1` times with the ascension rule. -/
noncomputable def expandOfficial (A : Arr r) (N : ℕ) : Arr r :=
  if A.len = 0 then A
  else if A.col (A.len - 1) 0 = 0 then dropLast A
  else
    let m := Nat.findGreatest (fun k => 0 < A.col (A.len - 1) k) (r - 1)
    let p := if h : HasParent A m (A.len - 1) then Classical.choose h else 0
    let s := A.len - 1 - p
    ⟨p + (N + 1) * s, tildeCol A p m s⟩

/-- **Remark 7.2**: on reachable arrays, Definition 5.1 agrees with the published rule. -/
theorem expandOfficial_eq_expand (hr : 0 < r) (hA : Reachable r A) (N : ℕ) :
    expandOfficial A N = expand A N := by
  by_cases h0 : A.len = 0
  · simp [expandOfficial, expand, h0]
  have hlen : 0 < A.len := Nat.pos_of_ne_zero h0
  by_cases hz : A.col (A.len - 1) 0 = 0
  · have hnot : ¬ LastHasParent A := (last_zero_iff hr hA hlen).mp hz
    rw [expand_of_not_lastHasParent h0 hnot]
    simp [expandOfficial, h0, hz]
  · have h : LastHasParent A := by
      by_contra hn
      exact hz ((last_zero_iff hr hA hlen).mpr hn)
    have hm : Nat.findGreatest (fun k => 0 < A.col (A.len - 1) k) (r - 1) = m₀ A :=
      (m₀_eq_findGreatest_pos hr hA h).symm
    simp only [expandOfficial, expand, h0, hz, h, if_false, if_true]
    rw [hm]
    rfl

end BM4
