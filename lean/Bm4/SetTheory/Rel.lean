/-
  Part III: relativization of a formula to a set variable `m` — the paper's `φ^M`, which restricts
  the *unbounded* quantifiers of `φ` to `m` and leaves the bounded ones as they are — its
  semantics, and Δ₀-definability of relativized predicates.
-/
import Bm4.SetTheory.Defin

universe u

namespace BM4.ST

namespace Fm

/-- Syntactic test for "`φ` is the body of a bounded quantifier `∀ i ∈ j`", i.e. `φ` has the shape
`i ∈ j → ψ` with `j ≠ i`.  Since `ball i j ψ` is by definition `all i (imp (mem i j) ψ)`, this is
exactly the distinction the paper makes between bounded and unbounded quantifiers. -/
def isBallBody (i : ℕ) : Fm → Bool
  | imp (mem i' j) _ => i' == i && j != i
  | _ => false

theorem isBallBody_iff (i : ℕ) : ∀ φ : Fm,
    isBallBody i φ = true ↔ ∃ j ψ, j ≠ i ∧ φ = imp (mem i j) ψ
  | falsum => by simp [isBallBody]
  | eq _ _ => by simp [isBallBody]
  | mem _ _ => by simp [isBallBody]
  | all _ _ => by simp [isBallBody]
  | imp falsum _ => by simp [isBallBody]
  | imp (eq _ _) _ => by simp [isBallBody]
  | imp (imp _ _) _ => by simp [isBallBody]
  | imp (all _ _) _ => by simp [isBallBody]
  | imp (mem a b) ψ => by
    simp only [isBallBody, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨rfl, hb⟩
      exact ⟨b, ψ, hb, rfl⟩
    · rintro ⟨j, ψ', hj, heq⟩
      obtain ⟨h1, -⟩ := Fm.imp.inj heq
      obtain ⟨rfl, rfl⟩ := Fm.mem.inj h1
      exact ⟨rfl, hj⟩

/-- The paper's `φ^M`: every **unbounded** quantifier of `φ` is restricted to `m`, while a
**bounded** quantifier `∀u ∈ a …` is left exactly as it stands. -/
def relTo (m : ℕ) : Fm → Fm
  | falsum => falsum
  | eq i j => eq i j
  | mem i j => mem i j
  | imp φ ψ => imp (relTo m φ) (relTo m ψ)
  | all i φ => if isBallBody i φ then all i (relTo m φ) else ball i m (relTo m φ)

/-- A bounded quantifier survives relativization untouched. -/
theorem relTo_ball (m i j : ℕ) (hij : i ≠ j) (ψ : Fm) :
    relTo m (ball i j ψ) = ball i j (relTo m ψ) := by
  show (if isBallBody i (imp (mem i j) ψ) then all i (relTo m (imp (mem i j) ψ))
      else ball i m (relTo m (imp (mem i j) ψ))) = _
  rw [if_pos ((isBallBody_iff i _).mpr ⟨j, ψ, Ne.symm hij, rfl⟩)]
  rfl

/-- An unbounded quantifier is restricted to `m`. -/
theorem relTo_all_of_not (m i : ℕ) (φ : Fm) (h : isBallBody i φ = false) :
    relTo m (all i φ) = ball i m (relTo m φ) := by
  show (if isBallBody i φ then _ else _) = _
  rw [if_neg (by simp [h])]

theorem relTo_delta0 (m : ℕ) : ∀ φ : Fm, m ∉ vars φ → IsDelta0 (relTo m φ)
  | falsum, _ => IsDelta0.falsum
  | eq i j, _ => IsDelta0.eq i j
  | mem i j, _ => IsDelta0.mem i j
  | imp φ ψ, h => by
    simp only [vars, Finset.mem_union, not_or] at h
    exact (relTo_delta0 m φ h.1).imp (relTo_delta0 m ψ h.2)
  | all i φ, h => by
    simp only [vars, Finset.mem_insert, not_or] at h
    have hIH : IsDelta0 (relTo m φ) := relTo_delta0 m φ h.2
    show IsDelta0 (if isBallBody i φ then all i (relTo m φ) else ball i m (relTo m φ))
    split_ifs with hb
    · obtain ⟨j, ψ, hj, rfl⟩ := (isBallBody_iff i φ).mp hb
      simp only [relTo] at hIH ⊢
      cases hIH with
      | imp _ h2 => exact IsDelta0.ball (Ne.symm hj) h2
    · exact IsDelta0.ball (fun e => h.1 e.symm) hIH

theorem fv_relTo_subset (m : ℕ) : ∀ φ : Fm, fv (relTo m φ) ⊆ insert m (fv φ)
  | falsum => by simp [relTo, fv]
  | eq i j => by simp [relTo, fv]
  | mem i j => by simp [relTo, fv]
  | imp φ ψ => by
    have h1 := fv_relTo_subset m φ
    have h2 := fv_relTo_subset m ψ
    simp only [relTo, fv]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_insert.mp (h1 hx) with rfl | hx'
      · simp
      · simp [hx']
    · rcases Finset.mem_insert.mp (h2 hx) with rfl | hx'
      · simp
      · simp [hx']
  | all i φ => by
    have hIH : fv (relTo m φ) ⊆ insert m (fv φ) := fv_relTo_subset m φ
    show fv (if isBallBody i φ then all i (relTo m φ) else ball i m (relTo m φ)) ⊆
      insert m (fv (all i φ))
    split_ifs with hb
    · simp only [fv]
      intro x hx
      rw [Finset.mem_erase] at hx
      rcases Finset.mem_insert.mp (hIH hx.2) with rfl | hx'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hx.1, hx'⟩)
    · simp only [fv_ball, fv]
      intro x hx
      rw [Finset.mem_erase] at hx
      rcases Finset.mem_union.mp hx.2 with hx' | hx'
      · rcases Finset.mem_insert.mp hx' with rfl | hx''
        · exact absurd rfl hx.1
        · rw [Finset.mem_singleton] at hx''
          subst hx''
          exact Finset.mem_insert_self _ _
      · rcases Finset.mem_insert.mp (hIH hx') with rfl | hx''
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hx.1, hx''⟩)

/-- Semantics of relativization.  Over a domain `D` containing the elements of the transitive set
`W = v m`, and for a valuation whose free values already lie in `W`, `relTo m φ` says exactly what
`φ` says with its quantifiers ranging over `W`.  The hypotheses on the parameters are needed
because the bounded quantifiers of `φ` are *not* restricted to `m`. -/
theorem sat_relTo {D : ZFSet.{u} → Prop} (m : ℕ) : ∀ (φ : Fm) (v : ℕ → ZFSet.{u}) (W : ZFSet.{u}),
    m ∉ vars φ → v m = W → TransDom (· ∈ W) → (∀ y ∈ fv φ, v y ∈ W) → (∀ x ∈ W, D x) →
    (Sat D v (relTo m φ) ↔ Sat (· ∈ W) v φ)
  | falsum, _, _, _, _, _, _, _ => Iff.rfl
  | eq i j, _, _, _, _, _, _, _ => Iff.rfl
  | mem i j, _, _, _, _, _, _, _ => Iff.rfl
  | imp φ ψ, v, W, hm, hvm, hT, hfv, hD => by
    simp only [vars, Finset.mem_union, not_or] at hm
    simp only [fv, Finset.mem_union] at hfv
    simp only [relTo, sat_imp]
    rw [sat_relTo m φ v W hm.1 hvm hT (fun y hy => hfv y (Or.inl hy)) hD,
      sat_relTo m ψ v W hm.2 hvm hT (fun y hy => hfv y (Or.inr hy)) hD]
  | all i φ, v, W, hm, hvm, hT, hfv, hD => by
    simp only [vars, Finset.mem_insert, not_or] at hm
    have him : i ≠ m := fun e => hm.1 e.symm
    have hupd : ∀ x : ZFSet.{u}, Function.update v i x m = v m :=
      fun x => Function.update_of_ne (Ne.symm him) _ _
    have IH : ∀ (w : ℕ → ZFSet.{u}), w m = W → (∀ y ∈ fv φ, w y ∈ W) →
        (Sat D w (relTo m φ) ↔ Sat (· ∈ W) w φ) :=
      fun w h1 h2 => sat_relTo m φ w W hm.2 h1 hT h2 hD
    have hupdW : ∀ x : ZFSet.{u}, Function.update v i x m = W := by
      intro x; rw [hupd]; exact hvm
    show Sat D v (if isBallBody i φ then all i (relTo m φ) else ball i m (relTo m φ)) ↔
      Sat (· ∈ W) v (all i φ)
    split_ifs with hb
    · obtain ⟨j, ψ, hj, rfl⟩ := (isBallBody_iff i φ).mp hb
      have hjW : v j ∈ W := by
        refine hfv j (Finset.mem_erase.mpr ⟨hj, ?_⟩)
        simp only [fv, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hmemW : ∀ x : ZFSet.{u}, x ∈ W →
          ∀ y ∈ fv (imp (mem i j) ψ), Function.update v i x y ∈ W := by
        intro x hx y hy
        by_cases hyi : y = i
        · subst hyi; rw [Function.update_self]; exact hx
        · rw [Function.update_of_ne hyi]
          exact hfv y (Finset.mem_erase.mpr ⟨hyi, hy⟩)
      simp only [sat_all]
      constructor
      · intro H x hx
        exact (IH (Function.update v i x) (hupdW x) (hmemW x hx)).mp (H x (hD x hx))
      · intro H x _
        simp only [relTo, sat_imp, sat_mem, Function.update_self, Function.update_of_ne hj]
        intro hxj
        have hxW : x ∈ W := hT (v j) hjW x hxj
        have hrel := (IH (Function.update v i x) (hupdW x) (hmemW x hxW)).mpr (H x hxW)
        simp only [relTo, sat_imp, sat_mem, Function.update_self,
          Function.update_of_ne hj] at hrel
        exact hrel hxj
    · have hmemW : ∀ x : ZFSet.{u}, x ∈ W → ∀ y ∈ fv φ, Function.update v i x y ∈ W := by
        intro x hx y hy
        by_cases hyi : y = i
        · subst hyi; rw [Function.update_self]; exact hx
        · rw [Function.update_of_ne hyi]
          exact hfv y (Finset.mem_erase.mpr ⟨hyi, hy⟩)
      rw [sat_ball_of_ne him, hvm, sat_all]
      constructor
      · intro H x hx
        exact (IH (Function.update v i x) (hupdW x) (hmemW x hx)).mp (H x (hD x hx) hx)
      · intro H x _ hx
        exact (IH (Function.update v i x) (hupdW x) (hmemW x hx)).mpr (H x hx)

/-- Renaming the bound variables of `φ` away from `m` (and from a finite set `avoid`), keeping
the free variables. -/
def avoidMap (φ : Fm) (K : ℕ) : ℕ → ℕ := fun i => if i ∈ fv φ then i else i + K

theorem avoidMap_injective (φ : Fm) {K : ℕ} (hK : ∀ i ∈ fv φ, i < K) :
    Function.Injective (avoidMap φ K) := by
  intro i j hij
  unfold avoidMap at hij
  split_ifs at hij with hi hj hj
  · exact hij
  · have := hK i hi; omega
  · have := hK j hj; omega
  · omega

theorem fv_rename_avoidMap (φ : Fm) {K : ℕ} (hK : ∀ i ∈ fv φ, i < K) :
    fv (rename (avoidMap φ K) φ) = fv φ := by
  rw [fv_rename _ (avoidMap_injective φ hK)]
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩; simpa [avoidMap, hi]
  · intro hx; exact ⟨x, hx, by simp [avoidMap, hx]⟩

theorem sat_rename_avoidMap (φ : Fm) {K : ℕ} (hK : ∀ i ∈ fv φ, i < K) (D : ZFSet.{u} → Prop)
    (v : ℕ → ZFSet.{u}) : Sat D v (rename (avoidMap φ K) φ) ↔ Sat D v φ := by
  rw [sat_rename (avoidMap_injective φ hK)]
  apply sat_congr
  intro x hx
  simp [avoidMap, hx]

theorem notMem_vars_rename_avoidMap (φ : Fm) {K m : ℕ} (hK : ∀ i ∈ fv φ, i < K) (hmK : m < K)
    (hm : m ∉ fv φ) : m ∉ vars (rename (avoidMap φ K) φ) := by
  rw [vars_rename]
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  unfold avoidMap at hi
  split_ifs at hi with hif
  · subst hi; exact hm hif
  · omega

/-- Any formula has an equivalent one (same free variables, same Σ̂/Π̂ class) not using `m` as a
bound variable, provided `m` is not free. -/
theorem exists_avoid (φ : Fm) (m : ℕ) (hm : m ∉ fv φ) :
    ∃ φ' : Fm, m ∉ vars φ' ∧ fv φ' = fv φ ∧
      (∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), Sat D v φ' ↔ Sat D v φ) ∧
      (∀ q, IsSigma q φ → IsSigma q φ') ∧ (∀ q, IsPi q φ → IsPi q φ') := by
  let K := bound φ + m + 1
  have hK : ∀ i ∈ fv φ, i < K := fun i hi => by have := fv_lt_bound hi; omega
  refine ⟨rename (avoidMap φ K) φ, notMem_vars_rename_avoidMap φ hK (by omega) hm,
    fv_rename_avoidMap φ hK, sat_rename_avoidMap φ hK, fun q h => h.rename (avoidMap_injective φ hK),
    fun q h => h.rename (avoidMap_injective φ hK)⟩

end Fm

open Fm

/-! ### Relativizing a definable predicate to a set variable -/

/-- The relativization of a Σ̂q-definable predicate to the set named by the variable `m` is
Δ₀-definable: the witness is literally the relativized formula. -/
theorem SigmaDef.relativize {q : ℕ} {s : Finset ℕ} {P : Pred.{u}} (hP : SigmaDef q s P) (m : ℕ)
    (hm : m ∉ s) :
    ∃ Q : Pred.{u}, Delta0Def (insert m s) Q ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), GoodDom D → D (v m) → GoodDom (· ∈ v m) →
        ValD (· ∈ v m) s v → (Q D v ↔ P (· ∈ v m) v) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  have hmφ : m ∉ fv φ := fun h => hm (hfv h)
  obtain ⟨φ', hm', hfv', hequiv, -, -⟩ := Fm.exists_avoid φ m hmφ
  refine ⟨fun D v => Sat D v (relTo m φ'),
    ⟨relTo m φ', relTo_delta0 m φ' hm', ?_, fun _ _ _ _ => Iff.rfl⟩, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp (fv_relTo_subset m φ' hx) with rfl | hx'
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hfv (hfv' ▸ hx'))
  · intro D v hD hDm hDW hv
    have h1 : ∀ y ∈ fv φ', v y ∈ v m := fun y hy => hv y (hfv (hfv' ▸ hy))
    have h2 : ∀ x ∈ v m, D x := fun x hx => hD.2 (v m) hDm x hx
    show Sat D v (relTo m φ') ↔ P (· ∈ v m) v
    rw [sat_relTo m φ' v (v m) hm' rfl hDW.2 h1 h2, hequiv (· ∈ v m) v]
    exact hsat (· ∈ v m) v hDW hv

/-- The relativization of a Π̂q-definable predicate. -/
theorem PiDef.relativize {q : ℕ} {s : Finset ℕ} {P : Pred.{u}} (hP : PiDef q s P) (m : ℕ)
    (hm : m ∉ s) :
    ∃ Q : Pred.{u}, Delta0Def (insert m s) Q ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), GoodDom D → D (v m) → GoodDom (· ∈ v m) →
        ValD (· ∈ v m) s v → (Q D v ↔ P (· ∈ v m) v) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  have hmφ : m ∉ fv φ := fun h => hm (hfv h)
  obtain ⟨φ', hm', hfv', hequiv, -, -⟩ := Fm.exists_avoid φ m hmφ
  refine ⟨fun D v => Sat D v (relTo m φ'),
    ⟨relTo m φ', relTo_delta0 m φ' hm', ?_, fun _ _ _ _ => Iff.rfl⟩, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp (fv_relTo_subset m φ' hx) with rfl | hx'
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hfv (hfv' ▸ hx'))
  · intro D v hD hDm hDW hv
    have h1 : ∀ y ∈ fv φ', v y ∈ v m := fun y hy => hv y (hfv (hfv' ▸ hy))
    have h2 : ∀ x ∈ v m, D x := fun x hx => hD.2 (v m) hDm x hx
    show Sat D v (relTo m φ') ↔ P (· ∈ v m) v
    rw [sat_relTo m φ' v (v m) hm' rfl hDW.2 h1 h2, hequiv (· ∈ v m) v]
    exact hsat (· ∈ v m) v hDW hv

end BM4.ST
