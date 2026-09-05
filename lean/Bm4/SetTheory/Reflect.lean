/-
  Part III, §17: finite pattern reflection (Theorem 17.1), and the resulting instance of the
  `LabelSystem` interface consumed by Parts IV and V.
-/
import Bm4.SetTheory.StKP
import Bm4.SetTheory.AdmKP
import Bm4.SetTheory.Stable
import Bm4.Label
import Bm4.Main

universe u

namespace BM4.ST

open Fm

theorem AdmOrd.le_def {a b : AdmOrd.{u}} : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

/-! ### Generic definability helpers -/

/-- A Π̂q predicate is Σ̂(q+1): put a dummy existential quantifier in front. -/
theorem PiDef.toSigma {q : ℕ} {S : Finset ℕ} {P : Pred.{u}} (h : PiDef q S P) :
    SigmaDef (q + 1) S P := by
  have hnot : fresh S ∉ S := fresh_notMem S
  have h2 := h.ex (fresh S)
  rw [Finset.erase_eq_of_notMem hnot] at h2
  refine h2.congr ?_
  intro D v hD hv
  have key : ∀ x : ZFSet.{u}, D x → (P D (Function.update v (fresh S) x) ↔ P D v) := by
    intro x _
    refine h.congr_val hD (fun k hk => ?_) hv (fun k hk => ?_)
    · rw [Function.update_of_ne (by rintro rfl; exact hnot hk)]
      exact hv k hk
    · exact Function.update_of_ne (by rintro rfl; exact hnot hk) _ _
  constructor
  · rintro ⟨x, hx, hP⟩
    exact (key x hx).mp hP
  · intro hP
    obtain ⟨x, hx⟩ := hD.1
    exact ⟨x, hx, (key x hx).mpr hP⟩

/-- A hypothesis not depending on the domain may be added in front. -/
theorem SigmaDef.imp_const {q : ℕ} {S : Finset ℕ} {P : Pred.{u}} (H : Prop)
    (h : SigmaDef q S P) : SigmaDef q S (fun D v => H → P D v) := by
  by_cases hH : H
  · exact h.congr (fun _ _ _ _ => ⟨fun hp _ => hp, fun hp => hp hH⟩)
  · exact ((Delta0Def.top.sigma q).mono (Finset.empty_subset S)).congr
      (fun _ _ _ _ => ⟨fun _ hh => absurd hh hH, fun _ => trivial⟩)

/-- Conjunction of two predicates with the same support. -/
theorem SigmaDef.and' {q : ℕ} {S : Finset ℕ} {P Q : Pred.{u}} (hP : SigmaDef q S P)
    (hQ : SigmaDef q S Q) : SigmaDef q S (fun D v => P D v ∧ Q D v) :=
  (hP.and hQ).mono (by simp)

/-- A finite conjunction indexed by a list. -/
theorem sigmaDef_bigAnd {q : ℕ} {S : Finset ℕ} {ι : Type} (P : ι → Pred.{u}) :
    ∀ l : List ι, (∀ c ∈ l, SigmaDef q S (P c)) →
      SigmaDef q S (fun D v => ∀ c ∈ l, P c D v) := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ((Delta0Def.top.sigma q).mono (Finset.empty_subset S)).congr ?_
    intro D v _ _
    simp
  | cons c t ih =>
    intro h
    refine ((h c (by simp)).and' (ih (fun d hd => h d (by simp [hd])))).congr ?_
    intro D v _ _
    exact (List.forall_mem_cons (p := fun c => P c D v)).symm

/-! ### An existential block over the variables `2, …, t + 1` -/

/-- `v` with the variables `2, …, t + 1` reset to `F 0, …, F (t-1)`. -/
def setBlk (t : ℕ) (F v : ℕ → ZFSet.{u}) (k : ℕ) : ZFSet.{u} :=
  if 2 ≤ k ∧ k < 2 + t then F (k - 2) else v k

theorem setBlk_zero (F v : ℕ → ZFSet.{u}) : setBlk 0 F v = v := by
  funext k
  simp only [setBlk]
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

theorem setBlk_out {t : ℕ} (F v : ℕ → ZFSet.{u}) {k : ℕ} (hk : k < 2 ∨ 2 + t ≤ k) :
    setBlk t F v k = v k := by
  simp only [setBlk]
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

theorem setBlk_mid {t : ℕ} (F v : ℕ → ZFSet.{u}) {i : ℕ} (hi : i < t) :
    setBlk t F v (2 + i) = F i := by
  simp only [setBlk]
  split_ifs with h
  · congr 1
    omega
  · exact absurd (show 2 ≤ 2 + i ∧ 2 + i < 2 + t by omega) h

theorem setBlk_succ (t : ℕ) (F v : ℕ → ZFSet.{u}) (x : ZFSet.{u}) :
    setBlk t F (Function.update v (2 + t) x) = setBlk (t + 1) (Function.update F t x) v := by
  funext k
  by_cases h1 : 2 ≤ k ∧ k < 2 + t
  · simp only [setBlk]
    rw [if_pos h1, if_pos (show 2 ≤ k ∧ k < 2 + (t + 1) by omega),
      Function.update_of_ne (show k - 2 ≠ t by omega)]
  · simp only [setBlk]
    rw [if_neg h1]
    by_cases h2 : k = 2 + t
    · subst h2
      rw [Function.update_self, if_pos (show 2 ≤ 2 + t ∧ 2 + t < 2 + (t + 1) by omega),
        show 2 + t - 2 = t by omega, Function.update_self]
    · rw [Function.update_of_ne h2, if_neg (by omega)]

theorem sigmaDef_blk {q : ℕ} (hq : 1 ≤ q) {P : Pred.{u}} :
    ∀ (t : ℕ) (S : Finset ℕ), SigmaDef q S P →
      SigmaDef q S
        (fun D v => ∃ F : ℕ → ZFSet.{u}, (∀ i, i < t → D (F i)) ∧ P D (setBlk t F v)) := by
  intro t
  induction t with
  | zero =>
    intro S hP
    refine hP.congr ?_
    intro D v _ _
    constructor
    · intro h
      exact ⟨fun _ => ∅, fun i hi => absurd hi (by omega), by rwa [setBlk_zero]⟩
    · rintro ⟨F, -, h⟩
      rwa [setBlk_zero] at h
  | succ t ih =>
    intro S hP
    refine (((ih S hP).ex (2 + t) hq).mono
      (fun z hz => Finset.mem_of_mem_erase hz)).congr ?_
    intro D v _ _
    constructor
    · rintro ⟨x, hx, F, hF, hbody⟩
      refine ⟨Function.update F t x, fun i hi => ?_, ?_⟩
      · by_cases hit : i = t
        · subst hit; rwa [Function.update_self]
        · rw [Function.update_of_ne hit]; exact hF i (by omega)
      · rwa [← setBlk_succ]
    · rintro ⟨F, hF, hbody⟩
      refine ⟨F t, hF t (by omega), F, fun i hi => hF i (by omega), ?_⟩
      rw [setBlk_succ, Function.update_eq_self]
      exact hbody


/-! ### Theorem 17.1: finite pattern reflection -/

theorem reflect_pattern (r n : ℕ) (α β : AdmOrd.{u}) (hnr : n < r) (hαβ : RelAdm n α β)
    (X : Finset AdmOrd.{u}) (hX : ∀ x ∈ X, x < α)
    (s : ℕ) (y : ℕ → AdmOrd.{u}) (hs : 0 < s)
    (hy : ∀ i j, i < j → j < s → y i < y j)
    (hαy : ∀ i, i < s → α ≤ y i) (hyβ : ∀ i, i < s → y i < β) :
    ∃ y' : ℕ → AdmOrd.{u},
      (∀ i j, i < j → j < s → y' i < y' j) ∧
      (∀ i, i < s → y' i < α) ∧
      (∀ x ∈ X, x < y' 0) ∧
      (∀ x ∈ X, ∀ i, i < s → ∀ k, k < r → RelAdm k x (y i) → RelAdm k x (y' i)) ∧
      (∀ i j, i < s → j < s → ∀ k, k < r → RelAdm k (y i) (y j) → RelAdm k (y' i) (y' j)) ∧
      (∀ i, i < s → ∀ m, m < n → RelAdm m (y i) β → RelAdm m (y' i) α) := by
  classical
  have hαg : GoodOrd α.1 := goodOrd_of_isAdmissible α.2
  have hβg : GoodOrd β.1 := goodOrd_of_isAdmissible β.2
  have hyg : ∀ i, GoodOrd (y i).1 := fun i => goodOrd_of_isAdmissible (y i).2
  -- enumerate the finite parameter set `X`
  obtain ⟨N, xf, hxfX, hxfsurj⟩ :
      ∃ (N : ℕ) (xf : ℕ → AdmOrd.{u}), (∀ a, a < N → xf a ∈ X) ∧
        (∀ x ∈ X, ∃ a, a < N ∧ xf a = x) := by
    refine ⟨X.toList.length, fun a => X.toList.getD a α, ?_, ?_⟩
    · intro a ha
      dsimp only
      rw [List.getD_eq_getElem _ _ ha]
      exact Finset.mem_toList.mp (List.getElem_mem ha)
    · intro x hx
      obtain ⟨a, ha, hax⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hx)
      refine ⟨a, ha, ?_⟩
      dsimp only
      rw [List.getD_eq_getElem _ _ ha]
      exact hax
  have hxfα : ∀ a, a < N → xf a < α := fun a ha => hX _ (hxfX a ha)
  have hxg : ∀ a, GoodOrd (xf a).1 := fun a => goodOrd_of_isAdmissible (xf a).2
  -- the valuation of the parameter variables
  obtain ⟨vP, hvP0, hvP1, hvPx, hvPα⟩ :
      ∃ vP : ℕ → ZFSet.{u}, vP 0 = L.{u} Ordinal.omega0.{u} ∧ vP 1 = ωZ.{u} ∧
        (∀ a, a < N → vP (2 + s + a) = ((xf a).1).toZFSet) ∧ (∀ k, vP k ∈ L α.1) := by
    refine ⟨fun k => if k = 0 then L.{u} Ordinal.omega0.{u} else if k = 1 then ωZ.{u}
        else if 2 + s ≤ k ∧ k < 2 + s + N then ((xf (k - (2 + s))).1).toZFSet else ∅,
      by simp, by norm_num, ?_, ?_⟩
    · intro a ha
      dsimp only
      rw [if_neg (show ¬ (2 + s + a = 0) by omega), if_neg (show ¬ (2 + s + a = 1) by omega),
        if_pos (show 2 + s ≤ 2 + s + a ∧ 2 + s + a < 2 + s + N by omega),
        show 2 + s + a - (2 + s) = a by omega]
    · intro k
      dsimp only
      by_cases h0 : k = 0
      · subst h0; simpa using hαg.Lomega_mem
      · by_cases h1 : k = 1
        · subst h1
          rw [if_neg h0, if_pos rfl]
          exact hαg.omegaZ_mem
        · rw [if_neg h0, if_neg h1]
          by_cases h2 : 2 + s ≤ k ∧ k < 2 + s + N
          · rw [if_pos h2]
            exact hαg.toZFSet_mem (AdmOrd.lt_def.mp (hxfα _ (by omega)))
          · rw [if_neg h2]
            exact hαg.wClosed.empty_mem
  obtain ⟨Fy, hFy⟩ : ∃ f : ℕ → ZFSet.{u}, f = fun i => ((y i).1).toZFSet := ⟨_, rfl⟩
  have hFyval : ∀ i, Fy i = ((y i).1).toZFSet := by intro i; rw [hFy]
  have e0 : ∀ F : ℕ → ZFSet.{u}, setBlk s F vP 0 = L.{u} Ordinal.omega0.{u} := by
    intro F; rw [setBlk_out F vP (Or.inl (by omega))]; exact hvP0
  have e1 : ∀ F : ℕ → ZFSet.{u}, setBlk s F vP 1 = ωZ.{u} := by
    intro F; rw [setBlk_out F vP (Or.inl (by omega))]; exact hvP1
  have ex : ∀ (F : ℕ → ZFSet.{u}) a, a < N → setBlk s F vP (2 + s + a) = ((xf a).1).toZFSet := by
    intro F a ha; rw [setBlk_out F vP (Or.inr (by omega))]; exact hvPx a ha
  have emid : ∀ (F : ℕ → ZFSet.{u}) i, i < s → setBlk s F vP (2 + i) = F i :=
    fun F i hi => setBlk_mid F vP hi
  have emid0 : ∀ F : ℕ → ZFSet.{u}, setBlk s F vP 2 = F 0 := by
    intro F; simpa using setBlk_mid F vP hs
  -- support bookkeeping
  have hsub2 : ∀ a b : ℕ, a < 2 + s + N → b < 2 + s + N →
      ({a, b} : Finset ℕ) ⊆ Finset.range (2 + s + N) := by
    intro a b ha hb z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_range]
    rcases hz with h | h <;> omega
  have hsub3 : ∀ a b c : ℕ, a < 2 + s + N → b < 2 + s + N → c < 2 + s + N →
      ({a, b, c} : Finset ℕ) ⊆ Finset.range (2 + s + N) := by
    intro a b c ha hb hc z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_range]
    rcases hz with h | h | h <;> omega
  have hsub4 : ∀ a b c d : ℕ, a < 2 + s + N → b < 2 + s + N → c < 2 + s + N → d < 2 + s + N →
      ({a, b, c, d} : Finset ℕ) ⊆ Finset.range (2 + s + N) := by
    intro a b c d ha hb hc hd z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_range]
    rcases hz with h | h | h | h <;> omega
  -- the matrix of the reflected formula, and its complexity
  have hbody : SigmaDef.{u} (n + 2) (Finset.range (2 + s + N)) (fun D v =>
      (∀ i ∈ List.range s, AdmKP D (v 0) (v 1) (v (2 + i))) ∧
      (∀ a ∈ List.range N, v (2 + s + a) ∈ v 2) ∧
      (∀ j ∈ List.range s, ∀ i ∈ List.range j, v (2 + i) ∈ v (2 + j)) ∧
      (∀ k ∈ List.range r, ∀ a ∈ List.range N, ∀ i ∈ List.range s,
        RelAdm k (xf a) (y i) → RelKP D (v 0) (v 1) k (v (2 + s + a)) (v (2 + i))) ∧
      (∀ k ∈ List.range r, ∀ j ∈ List.range s, ∀ i ∈ List.range j,
        RelAdm k (y i) (y j) → RelKP D (v 0) (v 1) k (v (2 + i)) (v (2 + j))) ∧
      (∀ m ∈ List.range n, ∀ i ∈ List.range s,
        RelAdm m (y i) β → StKP D (v 0) (v 1) m (v (2 + i)))) := by
    refine SigmaDef.and' ?_ (SigmaDef.and' ?_ (SigmaDef.and' ?_
      (SigmaDef.and' ?_ (SigmaDef.and' ?_ ?_))))
    · refine sigmaDef_bigAnd
        (fun i => fun (D : ZFSet.{u} → Prop) v => AdmKP D (v 0) (v 1) (v (2 + i))) _ ?_
      intro i hi
      have hi' : i < s := List.mem_range.mp hi
      exact ((sigmaDef_admKP 0 1 (2 + i) (by omega) (by omega) (by omega)).mono
        (hsub3 0 1 (2 + i) (by omega) (by omega) (by omega))).pad (by omega)
    · refine sigmaDef_bigAnd
        (fun a => fun (_ : ZFSet.{u} → Prop) v => v (2 + s + a) ∈ v 2) _ ?_
      intro a ha
      have ha' : a < N := List.mem_range.mp ha
      exact ((Delta0Def.mem (2 + s + a) 2).sigma (n + 2)).mono
        (hsub2 _ _ (by omega) (by omega))
    · refine sigmaDef_bigAnd (fun j => fun (_ : ZFSet.{u} → Prop) v =>
        ∀ i ∈ List.range j, v (2 + i) ∈ v (2 + j)) _ ?_
      intro j hj
      have hj' : j < s := List.mem_range.mp hj
      refine sigmaDef_bigAnd
        (fun i => fun (_ : ZFSet.{u} → Prop) v => v (2 + i) ∈ v (2 + j)) _ ?_
      intro i hi
      have hi' : i < j := List.mem_range.mp hi
      exact ((Delta0Def.mem (2 + i) (2 + j)).sigma (n + 2)).mono
        (hsub2 _ _ (by omega) (by omega))
    · refine sigmaDef_bigAnd (fun k => fun (D : ZFSet.{u} → Prop) v =>
        ∀ a ∈ List.range N, ∀ i ∈ List.range s,
          RelAdm k (xf a) (y i) → RelKP D (v 0) (v 1) k (v (2 + s + a)) (v (2 + i))) _ ?_
      intro k _
      refine sigmaDef_bigAnd (fun a => fun (D : ZFSet.{u} → Prop) v =>
        ∀ i ∈ List.range s,
          RelAdm k (xf a) (y i) → RelKP D (v 0) (v 1) k (v (2 + s + a)) (v (2 + i))) _ ?_
      intro a ha
      have ha' : a < N := List.mem_range.mp ha
      refine sigmaDef_bigAnd (fun i => fun (D : ZFSet.{u} → Prop) v =>
        RelAdm k (xf a) (y i) → RelKP D (v 0) (v 1) k (v (2 + s + a)) (v (2 + i))) _ ?_
      intro i hi
      have hi' : i < s := List.mem_range.mp hi
      exact SigmaDef.imp_const _
        (((sigmaDef_RelKP k 0 1 (2 + s + a) (2 + i) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)).mono
            (hsub4 _ _ _ _ (by omega) (by omega) (by omega) (by omega))).pad (by omega))
    · refine sigmaDef_bigAnd (fun k => fun (D : ZFSet.{u} → Prop) v =>
        ∀ j ∈ List.range s, ∀ i ∈ List.range j,
          RelAdm k (y i) (y j) → RelKP D (v 0) (v 1) k (v (2 + i)) (v (2 + j))) _ ?_
      intro k _
      refine sigmaDef_bigAnd (fun j => fun (D : ZFSet.{u} → Prop) v =>
        ∀ i ∈ List.range j,
          RelAdm k (y i) (y j) → RelKP D (v 0) (v 1) k (v (2 + i)) (v (2 + j))) _ ?_
      intro j hj
      have hj' : j < s := List.mem_range.mp hj
      refine sigmaDef_bigAnd (fun i => fun (D : ZFSet.{u} → Prop) v =>
        RelAdm k (y i) (y j) → RelKP D (v 0) (v 1) k (v (2 + i)) (v (2 + j))) _ ?_
      intro i hi
      have hi' : i < j := List.mem_range.mp hi
      exact SigmaDef.imp_const _
        (((sigmaDef_RelKP k 0 1 (2 + i) (2 + j) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)).mono
            (hsub4 _ _ _ _ (by omega) (by omega) (by omega) (by omega))).pad (by omega))
    · refine sigmaDef_bigAnd (fun m => fun (D : ZFSet.{u} → Prop) v =>
        ∀ i ∈ List.range s, RelAdm m (y i) β → StKP D (v 0) (v 1) m (v (2 + i))) _ ?_
      intro m hm
      have hm' : m < n := List.mem_range.mp hm
      refine sigmaDef_bigAnd (fun i => fun (D : ZFSet.{u} → Prop) v =>
        RelAdm m (y i) β → StKP D (v 0) (v 1) m (v (2 + i))) _ ?_
      intro i hi
      have hi' : i < s := List.mem_range.mp hi
      exact SigmaDef.imp_const _
        ((((piDef_StKP m 0 1 (2 + i) (by omega) (by omega) (by omega)).mono
          (hsub3 _ _ _ (by omega) (by omega) (by omega))).toSigma).pad (by omega))
  -- put the existential block in front
  obtain ⟨φ, hφ, hfvφ, hsatφ⟩ := sigmaDef_blk (q := n + 2) (by omega) s
    (Finset.range (2 + s + N)) hbody
  have hDα : GoodDom (· ∈ L α.1) := goodDom_mem (L_transitive α.1) ⟨ωZ, hαg.omegaZ_mem⟩
  have hDβ : GoodDom (· ∈ L β.1) := goodDom_mem (L_transitive β.1) ⟨ωZ, hβg.omegaZ_mem⟩
  have hαβ1 : α.1 < β.1 := AdmOrd.lt_def.mp hαβ.1
  have hLsub : L α.1 ⊆ L β.1 := L_mono hαβ1.le
  have hvalα : ValD (· ∈ L α.1) (Finset.range (2 + s + N)) vP := fun k _ => hvPα k
  have hvalβ : ValD (· ∈ L β.1) (Finset.range (2 + s + N)) vP := fun k _ => hLsub (hvPα k)
  -- the pattern is true in `L β`
  have hβsat : Sat (· ∈ L β.1) vP φ := by
    rw [hsatφ _ vP hDβ hvalβ]
    refine ⟨Fy, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hFyval i]
      exact hβg.toZFSet_mem (AdmOrd.lt_def.mp (hyβ i hi))
    · intro i hi
      have hi' : i < s := List.mem_range.mp hi
      rw [e0 Fy, e1 Fy, emid Fy i hi', hFyval i]
      exact (admKP_iff β.2 (AdmOrd.lt_def.mp (hyβ i hi'))).mpr (y i).2
    · intro a ha
      have ha' : a < N := List.mem_range.mp ha
      rw [ex Fy a ha', emid0 Fy, hFyval 0]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
        (lt_of_lt_of_le (AdmOrd.lt_def.mp (hxfα a ha')) (AdmOrd.le_def.mp (hαy 0 hs)))
    · intro j hj i hi
      have hj' : j < s := List.mem_range.mp hj
      have hi' : i < j := List.mem_range.mp hi
      rw [emid Fy i (by omega), emid Fy j hj', hFyval i, hFyval j]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (AdmOrd.lt_def.mp (hy i j hi' hj'))
    · intro k _ a ha i hi hrel
      have ha' : a < N := List.mem_range.mp ha
      have hi' : i < s := List.mem_range.mp hi
      rw [e0 Fy, e1 Fy, ex Fy a ha', emid Fy i hi', hFyval i]
      exact (relKP_iff hβg (hyg i) (hxg a) (AdmOrd.lt_def.mp hrel.1)
        (AdmOrd.lt_def.mp (hyβ i hi')) k).mpr hrel.2
    · intro k _ j hj i hi hrel
      have hj' : j < s := List.mem_range.mp hj
      have hi' : i < j := List.mem_range.mp hi
      rw [e0 Fy, e1 Fy, emid Fy i (by omega), emid Fy j hj', hFyval i, hFyval j]
      exact (relKP_iff hβg (hyg j) (hyg i) (AdmOrd.lt_def.mp hrel.1)
        (AdmOrd.lt_def.mp (hyβ j hj')) k).mpr hrel.2
    · intro m _ i hi hrel
      have hi' : i < s := List.mem_range.mp hi
      rw [e0 Fy, e1 Fy, emid Fy i hi', hFyval i]
      exact (stKP_iff hβg (hyg i) (AdmOrd.lt_def.mp (hyβ i hi')) m).mpr hrel.2
  -- reflect it down to `L α`
  have hαsat : Sat (· ∈ L α.1) vP φ :=
    (hαβ.2.sigma (le_refl (n + 2)) hφ (fun x _ => hvPα x)).mpr hβsat
  obtain ⟨F, hFmem, hBody⟩ := (hsatφ _ vP hDα hvalα).mp hαsat
  -- the witnesses are codes of admissible ordinals below `α`
  have hAdmF : ∀ i, i < s → AdmKP (· ∈ L α.1) (L.{u} Ordinal.omega0.{u}) ωZ.{u} (F i) := by
    intro i hi
    have h := hBody.1 i (List.mem_range.mpr hi)
    rwa [e0 F, e1 F, emid F i hi] at h
  have hFord : ∀ i, i < s → (F i).IsOrdinal := by
    intro i hi
    obtain ⟨M, -, c, -, U, -, S, -, hlc, -, -⟩ := hAdmF i hi
    obtain ⟨U1, H1, S1, D1, hfc1, hc1, hrest1⟩ := hlc
    exact hc1.1
  have hFrank : ∀ i, i < s → ((F i).rank).toZFSet = F i := fun i hi => (hFord i hi).toZFSet_rank_eq
  have hFlt : ∀ i, i < s → (F i).rank < α.1 := by
    intro i hi
    have h := hFmem i hi
    rw [← hFrank i hi] at h
    exact (toZFSet_mem_L_iff _ _).mp h
  have hFadm : ∀ i, i < s → IsAdmissible ((F i).rank) := by
    intro i hi
    refine (admKP_iff α.2 (hFlt i hi)).mp ?_
    rw [hFrank i hi]
    exact hAdmF i hi
  have hall : ∀ i : ℕ, IsAdmissible (if i < s then (F i).rank else (F 0).rank) := by
    intro i
    split_ifs with h
    · exact hFadm i h
    · exact hFadm 0 hs
  obtain ⟨y', hy'def⟩ : ∃ f : ℕ → AdmOrd.{u},
      f = fun i => (⟨if i < s then (F i).rank else (F 0).rank, hall i⟩ : AdmOrd.{u}) := ⟨_, rfl⟩
  have hy'val : ∀ i, i < s → (y' i).1 = (F i).rank := by
    intro i hi
    simp only [hy'def]
    exact if_pos hi
  have hy'F : ∀ i, i < s → ((y' i).1).toZFSet = F i := by
    intro i hi; rw [hy'val i hi]; exact hFrank i hi
  have hy'α : ∀ i, i < s → (y' i).1 < α.1 := by
    intro i hi; rw [hy'val i hi]; exact hFlt i hi
  have hy'g : ∀ i, GoodOrd (y' i).1 := fun i => goodOrd_of_isAdmissible (y' i).2
  have hmono : ∀ i j, i < j → j < s → y' i < y' j := by
    intro i j hij hj
    have h := hBody.2.2.1 j (List.mem_range.mpr hj) i (List.mem_range.mpr hij)
    rw [emid F i (by omega), emid F j hj, ← hy'F i (by omega), ← hy'F j hj] at h
    exact AdmOrd.lt_def.mpr (Ordinal.toZFSet_mem_toZFSet_iff.mp h)
  have hle : ∀ i, i < s → y' 0 ≤ y' i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | h
    · exact le_rfl
    · exact (hmono 0 i h hi).le
  have hXlt : ∀ x ∈ X, x < y' 0 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hxfsurj x hx
    have h := hBody.2.1 a (List.mem_range.mpr ha)
    rw [ex F a ha, emid0 F, ← hy'F 0 hs] at h
    exact AdmOrd.lt_def.mpr (Ordinal.toZFSet_mem_toZFSet_iff.mp h)
  refine ⟨y', hmono, fun i hi => AdmOrd.lt_def.mpr (hy'α i hi), hXlt, ?_, ?_, ?_⟩
  · intro x hx i hi k hk hrel
    obtain ⟨a, ha, rfl⟩ := hxfsurj x hx
    have h := hBody.2.2.2.1 k (List.mem_range.mpr hk) a (List.mem_range.mpr ha) i
      (List.mem_range.mpr hi) hrel
    rw [e0 F, e1 F, ex F a ha, emid F i hi, ← hy'F i hi] at h
    have hlt : xf a < y' i := lt_of_lt_of_le (hXlt _ (hxfX a ha)) (hle i hi)
    exact ⟨hlt, (relKP_iff hαg (hy'g i) (hxg a) (AdmOrd.lt_def.mp hlt) (hy'α i hi) k).mp h⟩
  · intro i j hi hj k hk hrel
    have hij : i < j := by
      rcases lt_trichotomy i j with h | h | h
      · exact h
      · subst h; exact absurd hrel.1 (lt_irrefl _)
      · exact absurd hrel.1 (not_lt.mpr (hy j i h hi).le)
    have h := hBody.2.2.2.2.1 k (List.mem_range.mpr hk) j (List.mem_range.mpr hj) i
      (List.mem_range.mpr hij) hrel
    rw [e0 F, e1 F, emid F i (by omega), emid F j hj, ← hy'F i (by omega), ← hy'F j hj] at h
    have hlt : y' i < y' j := hmono i j hij hj
    exact ⟨hlt, (relKP_iff hαg (hy'g j) (hy'g i) (AdmOrd.lt_def.mp hlt) (hy'α j hj) k).mp h⟩
  · intro i hi m hm hrel
    have h := hBody.2.2.2.2.2 m (List.mem_range.mpr hm) i (List.mem_range.mpr hi) hrel
    rw [e0 F, e1 F, emid F i hi, ← hy'F i hi] at h
    exact ⟨AdmOrd.lt_def.mpr (hy'α i hi), (stKP_iff hαg (hy'g i) (hy'α i hi) m).mp h⟩

/-! ### The label system of Part III -/

/-- The `LabelSystem` interface (Lemma 15.1, Lemma 16.2, Theorem 17.1), realised by the
admissible ordinals with the stability relations `◁ₖ`. -/
noncomputable def bm4LabelSystem : BM4.LabelSystem.{u + 1} where
  Lab := AdmOrd.{u}
  rel := RelAdm
  rel_lt := relAdm_lt
  rel_mono := relAdm_mono
  rel_trans := relAdm_trans
  init := exists_relAdm_all
  reflect := fun r n α β hnr hrel X hX s y hs hy hαy hyβ =>
    reflect_pattern r n α β hnr hrel X hX s y hs hy hαy hyβ

/-- **Theorem 1.2**: every expansion sequence of BM4 terminates (no hypotheses). -/
theorem terminates_unconditional {r : ℕ} (A : BM4.Arr r) (hA : BM4.Reachable r A) (n : ℕ → ℕ) :
    ∃ T, (BM4.seq A n T).len = 0 :=
  BM4.terminates bm4LabelSystem.{0} A hA n

/-- **Proposition 22.1**: the one-step expansion relation of BM4 is well-founded. -/
theorem R_wf_unconditional (r : ℕ) : WellFounded (BM4.R r) :=
  BM4.R_wf bm4LabelSystem.{0} r

/-- **Theorem 1.2** on BM4 itself (Definition 1.1), i.e. on the union over all row counts. -/
theorem terminates_all_unconditional (A : BM4.Elts) (n : ℕ → ℕ) :
    ∃ T, (BM4.seq A.2.1 n T).len = 0 :=
  BM4.terminates_all bm4LabelSystem.{0} A n

/-- **Proposition 22.1** on BM4 itself. -/
theorem R'_wf_unconditional : WellFounded BM4.R' :=
  BM4.R'_wf bm4LabelSystem.{0}

end BM4.ST
