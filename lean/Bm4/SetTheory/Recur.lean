/-
  Part III (§10, semantic form): Σ1-Collection in an admissible `L θ`.
  Witness tuples are collected into finite sets so that Δ₀-Collection applies.
-/
import Bm4.SetTheory.HF
import Bm4.SetTheory.Rel

universe u

namespace BM4.ST

open Fm

/-- `ExsD D l P v`: there are values in `D` for the variables of `l` making `P` true. -/
def ExsD (D : ZFSet.{u} → Prop) : List ℕ → ((ℕ → ZFSet.{u}) → Prop) → (ℕ → ZFSet.{u}) → Prop
  | [], P, v => P v
  | i :: l, P, v => ∃ y, D y ∧ ExsD D l P (Function.update v i y)

/-- `ExsIn b l P v`: there are values in the set `b` for the variables of `l` making `P` true. -/
def ExsIn (b : ZFSet.{u}) : List ℕ → ((ℕ → ZFSet.{u}) → Prop) → (ℕ → ZFSet.{u}) → Prop
  | [], P, v => P v
  | i :: l, P, v => ∃ y ∈ b, ExsIn b l P (Function.update v i y)

theorem exsIn_mono {b b' : ZFSet.{u}} (hb : b ⊆ b') :
    ∀ (l : List ℕ) (P : (ℕ → ZFSet.{u}) → Prop) (v : ℕ → ZFSet.{u}), ExsIn b l P v → ExsIn b' l P v
  | [], _, _, h => h
  | i :: l, P, v, ⟨y, hy, h⟩ => ⟨y, hb hy, exsIn_mono hb l P _ h⟩

theorem exsIn_imp_exsD {D : ZFSet.{u} → Prop} {b : ZFSet.{u}} (hb : ∀ y ∈ b, D y) :
    ∀ (l : List ℕ) (P : (ℕ → ZFSet.{u}) → Prop) (v : ℕ → ZFSet.{u}), ExsIn b l P v → ExsD D l P v
  | [], _, _, h => h
  | i :: l, P, v, ⟨y, hy, h⟩ => ⟨y, hb y hy, exsIn_imp_exsD hb l P _ h⟩

theorem exsIn_congr {b : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop} (h : ∀ v, P v ↔ Q v) :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}), ExsIn b l P v ↔ ExsIn b l Q v
  | [], v => h v
  | i :: l, v => by
    simp only [ExsIn]
    apply exists_congr; intro y; apply and_congr_right; intro _
    exact exsIn_congr h l _

theorem exsD_congr {D : ZFSet.{u} → Prop} {P Q : (ℕ → ZFSet.{u}) → Prop} (h : ∀ v, P v ↔ Q v) :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}), ExsD D l P v ↔ ExsD D l Q v
  | [], v => h v
  | i :: l, v => by
    simp only [ExsD]
    apply exists_congr; intro y; apply and_congr_right; intro _
    exact exsD_congr h l _

/-- Updating a variable not in the block and irrelevant to `P` commutes with `ExsIn`. -/
theorem exsIn_update_of_notMem {b : ZFSet.{u}} {P : (ℕ → ZFSet.{u}) → Prop} {c : ℕ}
    (hP : ∀ v z, P (Function.update v c z) ↔ P v) :
    ∀ (l : List ℕ), c ∉ l → ∀ (v : ℕ → ZFSet.{u}) (z : ZFSet.{u}),
      ExsIn b l P (Function.update v c z) ↔ ExsIn b l P v
  | [], _, v, z => hP v z
  | i :: l, hc, v, z => by
    simp only [ExsIn]
    have hic : i ≠ c := fun h => hc (by simp [h])
    apply exists_congr; intro y; apply and_congr_right; intro _
    rw [Function.update_comm hic.symm]
    exact exsIn_update_of_notMem hP l (fun h => hc (by simp [h])) _ z

/-- Witnesses in `D` can be gathered into a finite list. -/
theorem exsD_exists_list {D : ZFSet.{u} → Prop} :
    ∀ (l : List ℕ) (P : (ℕ → ZFSet.{u}) → Prop) (v : ℕ → ZFSet.{u}), ExsD D l P v →
      ∃ ys : List ZFSet.{u}, (∀ y ∈ ys, D y) ∧ ExsIn (ofList ys) l P v
  | [], P, v, h => ⟨[], by simp, h⟩
  | i :: l, P, v, ⟨y, hy, h⟩ => by
    obtain ⟨ys, hys, h'⟩ := exsD_exists_list l P _ h
    refine ⟨y :: ys, ?_, y, by simp [mem_ofList], ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · exact hys z hz
    · exact exsIn_mono (fun z hz => by rw [mem_ofList] at hz ⊢; exact List.mem_cons_of_mem _ hz) l P _ h'

/-- `ExsIn (v c) l (Q D) v` is Δ₀-definable when `Q` is. -/
theorem delta0Def_exsIn {s : Finset ℕ} {Q : Pred.{u}} (hQ : Delta0Def s Q) (c : ℕ) (hc : c ∉ s) :
    ∀ (l : List ℕ), c ∉ l → Delta0Def (insert c s) (fun D v => ExsIn (v c) l (Q D) v)
  | [], _ => hQ.mono (Finset.subset_insert _ _)
  | i :: l, hcl => by
    have hic : i ≠ c := fun h => hcl (by simp [h])
    have ih := delta0Def_exsIn hQ c hc l (fun h => hcl (by simp [h]))
    have := (ih.bex i c hic)
    refine this.congr ?_ |>.mono ?_
    · intro D v _ _
      simp only [ExsIn]
      apply exists_congr; intro y; apply and_congr_right; intro _
      rw [Function.update_of_ne hic.symm]
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto

/-- Conditional congruence for `ExsD`: `P` and `P'` agree on valuations with values in `D` on `s`. -/
theorem exsD_congr_valD {D : ZFSet.{u} → Prop} {s : Finset ℕ} {P P' : (ℕ → ZFSet.{u}) → Prop}
    (h : ∀ w, ValD D s w → (P w ↔ P' w)) :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}), (∀ k ∈ s, k ∉ l → D (v k)) →
      (ExsD D l P v ↔ ExsD D l P' v)
  | [], v, hv => h v (fun k hk => hv k hk (by simp))
  | i :: l, v, hv => by
    simp only [ExsD]
    apply exists_congr; intro y; apply and_congr_right; intro hy
    apply exsD_congr_valD h l
    intro k hk hkl
    by_cases hki : k = i
    · subst hki; simpa
    · rw [Function.update_of_ne hki]; exact hv k hk (by simp [hki, hkl])

theorem exsIn_congr_valD {D : ZFSet.{u} → Prop} {b : ZFSet.{u}} (hb : ∀ y ∈ b, D y) {s : Finset ℕ}
    {P P' : (ℕ → ZFSet.{u}) → Prop} (h : ∀ w, ValD D s w → (P w ↔ P' w)) :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}), (∀ k ∈ s, k ∉ l → D (v k)) →
      (ExsIn b l P v ↔ ExsIn b l P' v)
  | [], v, hv => h v (fun k hk => hv k hk (by simp))
  | i :: l, v, hv => by
    simp only [ExsIn]
    apply exists_congr; intro y; apply and_congr_right; intro hy
    apply exsIn_congr_valD hb h l
    intro k hk hkl
    by_cases hki : k = i
    · subst hki; simpa using hb y hy
    · rw [Function.update_of_ne hki]; exact hv k hk (by simp [hki, hkl])

/-- `ExsD` only depends on the valuation outside the block (for `P` depending on `s`). -/
theorem exsD_congr_outside {D : ZFSet.{u} → Prop} {s : Finset ℕ} {P : (ℕ → ZFSet.{u}) → Prop}
    (hP : ∀ w w', (∀ k ∈ s, w k = w' k) → (P w ↔ P w')) :
    ∀ (l : List ℕ) (v v' : ℕ → ZFSet.{u}), (∀ k ∈ s, k ∉ l → v k = v' k) →
      (ExsD D l P v ↔ ExsD D l P v')
  | [], v, v', h => hP v v' (fun k hk => h k hk (by simp))
  | i :: l, v, v', h => by
    simp only [ExsD]
    apply exists_congr; intro y; apply and_congr_right; intro _
    apply exsD_congr_outside hP l
    intro k hk hkl
    by_cases hki : k = i
    · subst hki; simp
    · rw [Function.update_of_ne hki, Function.update_of_ne hki]; exact h k hk (by simp [hki, hkl])

theorem exsIn_congr_outside {b : ZFSet.{u}} {s : Finset ℕ} {P : (ℕ → ZFSet.{u}) → Prop}
    (hP : ∀ w w', (∀ k ∈ s, w k = w' k) → (P w ↔ P w')) :
    ∀ (l : List ℕ) (v v' : ℕ → ZFSet.{u}), (∀ k ∈ s, k ∉ l → v k = v' k) →
      (ExsIn b l P v ↔ ExsIn b l P v')
  | [], v, v', h => hP v v' (fun k hk => h k hk (by simp))
  | i :: l, v, v', h => by
    simp only [ExsIn]
    apply exists_congr; intro y; apply and_congr_right; intro _
    apply exsIn_congr_outside hP l
    intro k hk hkl
    by_cases hki : k = i
    · subst hki; simp
    · rw [Function.update_of_ne hki, Function.update_of_ne hki]; exact h k hk (by simp [hki, hkl])

/-- **Σ1-Collection** in an admissible `L θ`, for a Δ₀-definable matrix `Q` with a block `l` of
witness variables: if for every `x ∈ v a` there are witnesses in `L θ`, then there is a single
`b ∈ L θ` containing witnesses for all `x ∈ v a`. -/
theorem sigma1_collection {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {s : Finset ℕ} {Q : Pred.{u}}
    (hQ : Delta0Def s Q) (l : List ℕ) (i a : ℕ) (hia : i ≠ a) (hil : i ∉ l) (hal : a ∉ l)
    {v : ℕ → ZFSet.{u}} (hv : ∀ k ∈ s, k ∉ l → k ≠ i → v k ∈ L θ) (ha : v a ∈ L θ)
    (h : ∀ x ∈ v a, ExsD (· ∈ L θ) l (Q (· ∈ L θ)) (Function.update v i x)) :
    ∃ b ∈ L θ, ∀ x ∈ v a, ExsIn b l (Q (· ∈ L θ)) (Function.update v i x) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hQ
  set W := L θ with hW
  have hT := L_transitive θ
  have hWgood : GoodDom (· ∈ W) := hθ.goodDom
  have hlim := hθ.isSuccLimit
  -- the formula version of `Q`, independent of variables outside `fv φ`
  set Q' : Pred.{u} := fun D w => Sat D w φ with hQ'
  have hQQ' : ∀ w, ValD (· ∈ W) s w → (Q (· ∈ W) w ↔ Q' (· ∈ W) w) :=
    fun w hw => (hsat _ w hWgood hw).symm
  have hQ'def : Delta0Def s Q' := ⟨φ, hφ, hfv, fun _ _ _ _ => Iff.rfl⟩
  have hQ'cong : ∀ w w', (∀ k ∈ s, w k = w' k) → (Q' (· ∈ W) w ↔ Q' (· ∈ W) w') :=
    fun w w' hww' => sat_congr (fun k hk => hww' k (hfv hk))
  -- a fresh variable `c` for the finite witness set
  let c : ℕ := s.sup id + i + a + l.sum + 1
  have hcs : c ∉ s := fun hc => by have := Finset.le_sup (f := id) hc; simp only [id] at this; omega
  have hcl : c ∉ l := fun hc => by have := List.le_sum_of_mem hc; omega
  have hci : c ≠ i := by omega
  have hcφ : c ∉ fv φ := fun hc => hcs (hfv hc)
  have hP := delta0Def_exsIn hQ'def c hcs l hcl
  have hQ'c : ∀ w z, Q' (· ∈ W) (Function.update w c z) ↔ Q' (· ∈ W) w :=
    fun w z => sat_update_of_notMem hcφ z
  -- normalize the valuation on the block variables
  let v' : ℕ → ZFSet.{u} := fun k => if k ∈ l then ∅ else v k
  have hvv' : ∀ k, k ∉ l → v k = v' k := fun k hk => by simp [v', hk]
  have hv'a : v' a = v a := by simp [v', hal]
  have hv'W : ∀ k ∈ s, k ≠ i → v' k ∈ W := by
    intro k hk hki
    by_cases hkl : k ∈ l
    · simp only [v', hkl, if_true]; exact empty_mem_L_of_limit hlim
    · rw [← hvv' k hkl]; exact hv k hk hkl hki
  have hupd : ∀ x, ∀ k ∈ s, k ∉ l → Function.update v i x k = Function.update v' i x k := by
    intro x k _ hkl
    by_cases hki : k = i
    · subst hki; simp
    · rw [Function.update_of_ne hki, Function.update_of_ne hki]; exact hvv' k hkl
  -- values on `s` (outside the block) of the updated valuations lie in `W`
  have hvx : ∀ x ∈ v a, ∀ k ∈ s, k ∉ l → Function.update v i x k ∈ W := by
    intro x hx k hk hkl
    by_cases hki : k = i
    · subst hki; simpa using hT.subset_of_mem ha hx
    · rw [Function.update_of_ne hki]; exact hv k hk hkl hki
  have hv'x : ∀ x ∈ v a, ∀ k ∈ s, k ≠ i → Function.update v' i x k ∈ W := by
    intro x hx k hk hki
    rw [Function.update_of_ne hki]; exact hv'W k hk hki
  -- switch to `Q'` and `v'`
  have h' : ∀ x ∈ v a, ExsD (· ∈ W) l (Q' (· ∈ W)) (Function.update v' i x) := by
    intro x hx
    rw [← exsD_congr_outside hQ'cong l _ _ (hupd x)]
    rw [← exsD_congr_valD hQQ' l _ (hvx x hx)]
    exact h x hx
  have hval : ValD (· ∈ W) (((insert c s).erase i).erase c) v' := by
    intro k hk
    simp only [Finset.mem_erase, Finset.mem_insert] at hk
    obtain ⟨hkc, hki, hk⟩ := hk
    rcases hk with rfl | hk
    · exact absurd rfl hkc
    · exact hv'W k hk hki
  have hwit : ∀ x ∈ v a, ∃ y ∈ W,
      (fun D w => ExsIn (w c) l (Q' D) w) (· ∈ W) (Function.update (Function.update v' i x) c y) := by
    intro x hx
    obtain ⟨ys, hys, hxys⟩ := exsD_exists_list l _ _ (h' x hx)
    refine ⟨ofList ys, ofList_mem_L_of_limit hlim ys hys, ?_⟩
    simp only [Function.update_self]
    rw [exsIn_update_of_notMem hQ'c l hcl]
    exact hxys
  obtain ⟨b₀, hb₀, hcoll⟩ := hθ.collection _ _ hP i c hci.symm v' hval (v a) ha hwit
  refine ⟨ZFSet.sUnion b₀, sUnion_mem_L_of_limit hlim hb₀, ?_⟩
  intro x hx
  obtain ⟨w, hw, hxw⟩ := hcoll x hx
  simp only [Function.update_self] at hxw
  have hsub : w ⊆ ZFSet.sUnion b₀ := fun z hz => ZFSet.mem_sUnion.mpr ⟨w, hw, hz⟩
  have h1 := exsIn_mono hsub l _ _ hxw
  rw [exsIn_update_of_notMem hQ'c l hcl] at h1
  have hbW : ∀ y ∈ ZFSet.sUnion b₀, y ∈ W := fun y hy => by
    obtain ⟨z, hz, hyz⟩ := ZFSet.mem_sUnion.mp hy
    exact hT.subset_of_mem (hT.subset_of_mem hb₀ hz) hyz
  rw [exsIn_congr_valD hbW hQQ' l _ (hvx x hx)]
  rw [exsIn_congr_outside hQ'cong l _ _ (hupd x)]
  exact h1

end BM4.ST
