/-
  Part III, §11: soundness and completeness of the recognizer `KPAxCode` for admissibility.

  Every formula whose code is recognised by `KPAxCode` is true in `L θ` for an admissible `θ`
  (`satIn_kpAx`), and conversely, if `η > ω` is a limit in which all of them are true, then `η`
  is admissible (`isAdmissible_of_kpTrue`).

  The recognised codes are universal closures, so `satIn_alls` / `sat_of_alls` here move between
  a closure and its instance.  Truth in `L θ` is taken with respect to valuations with values in
  `L θ`.
-/
import Bm4.SetTheory.KPAx

universe u

namespace BM4.ST

open Fm

/-! ### Valuations into `L θ` -/

/-- Updating a valuation with values in `W` by an element of `W` keeps all values in `W`. -/
theorem update_forall_mem {W : ZFSet.{u}} {v : ℕ → ZFSet.{u}} (hv : ∀ n, v n ∈ W) (i : ℕ)
    {x : ZFSet.{u}} (hx : x ∈ W) : ∀ n, Function.update v i x n ∈ W := by
  intro n
  by_cases h : n = i
  · subst h; simpa using hx
  · rw [Function.update_of_ne h]; exact hv n

/-! ### Universal closures and satisfaction -/

/-- A formula true under every valuation into `L θ` has all its universal closures true there. -/
theorem satIn_alls {θ : Ordinal.{u}} {χ : Fm}
    (H : ∀ v : ℕ → ZFSet.{u}, (∀ n, v n ∈ L θ) → SatIn (L θ) v χ) :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}), (∀ n, v n ∈ L θ) → SatIn (L θ) v (Fm.alls l χ) := by
  intro l
  induction l with
  | nil => intro v hv; exact H v hv
  | cons k l ih =>
    intro v hv
    rw [Fm.alls_cons]
    simp only [SatIn, sat_all]
    intro z hz
    exact ih _ (update_forall_mem hv k hz)

/-- Instantiating a universal block: from `Sat D v (alls l χ)` one gets `Sat D v₀ χ` for a
valuation `v₀` which is `v'` on `l` and `v` off `l`. -/
theorem sat_alls_elim {D : ZFSet.{u} → Prop} (v' : ℕ → ZFSet.{u}) (hv' : ∀ k, D (v' k)) :
    ∀ (l : List ℕ) (χ : Fm) (v : ℕ → ZFSet.{u}), Sat D v (Fm.alls l χ) →
      ∃ v₀ : ℕ → ZFSet.{u}, (∀ k ∈ l, v₀ k = v' k) ∧ (∀ m, m ∉ l → v₀ m = v m) ∧
        Sat D v₀ χ := by
  intro l
  induction l with
  | nil => intro χ v h; exact ⟨v, by simp, fun _ _ => rfl, h⟩
  | cons k l ih =>
    intro χ v h
    rw [Fm.alls_cons, sat_all] at h
    obtain ⟨v₀, h1, h2, h3⟩ := ih χ (Function.update v k (v' k)) (h (v' k) (hv' k))
    refine ⟨v₀, ?_, ?_, h3⟩
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · by_cases hml : m ∈ l
        · exact h1 m hml
        · rw [h2 m hml, Function.update_self]
      · exact h1 m hm
    · intro m hm
      rw [List.mem_cons, not_or] at hm
      rw [h2 m hm.2, Function.update_of_ne hm.1]

/-- The universal closure implies the instance, at the same valuation. -/
theorem sat_of_alls {D : ZFSet.{u} → Prop} {l : List ℕ} {χ : Fm} {v : ℕ → ZFSet.{u}}
    (hv : ∀ k, D (v k)) (h : Sat D v (Fm.alls l χ)) : Sat D v χ := by
  obtain ⟨v₀, h1, h2, h3⟩ := sat_alls_elim v hv l χ v h
  refine (sat_congr ?_).mp h3
  intro k _
  by_cases hk : k ∈ l
  · exact h1 k hk
  · exact h2 k hk

/-! ### The five closed axioms -/

theorem satIn_extAx {θ : Ordinal.{u}} (v : ℕ → ZFSet.{u}) : SatIn (L θ) v extAx := by
  have hT := L_transitive θ
  simp only [extAx, SatIn, sat_all, sat_imp, sat_iff, sat_eq, sat_mem]
  intro a ha b hb H
  simp (disch := omega) only [Function.update_self, Function.update_of_ne] at H ⊢
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (H z (hT.subset_of_mem ha hz)).mp hz
  · intro hz
    exact (H z (hT.subset_of_mem hb hz)).mpr hz

theorem satIn_emptyAx {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) (v : ℕ → ZFSet.{u}) :
    SatIn (L θ) v emptyAx := by
  simp only [emptyAx, SatIn, sat_ex, sat_all, sat_not, sat_mem]
  refine ⟨∅, empty_mem_L_of_limit hθ, ?_⟩
  intro y _
  simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  simp

theorem satIn_pairAx {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) (v : ℕ → ZFSet.{u}) :
    SatIn (L θ) v pairAx := by
  simp only [pairAx, SatIn, sat_all, sat_ex, sat_and, sat_mem]
  intro a ha b hb
  refine ⟨({a, b} : ZFSet.{u}), pair_mem_L_of_limit hθ ha hb, ?_⟩
  simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  exact ⟨mem_upair_left a b, mem_upair_right a b⟩

theorem satIn_unionAx {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) (v : ℕ → ZFSet.{u}) :
    SatIn (L θ) v unionAx := by
  simp only [unionAx, SatIn, sat_all, sat_ex]
  intro a ha
  refine ⟨ZFSet.sUnion a, sUnion_mem_L_of_limit hθ ha, ?_⟩
  rw [sat_ball_of_ne (show (2 : ℕ) ≠ 0 by decide)]
  intro b _ hb
  rw [sat_ball_of_ne (show (3 : ℕ) ≠ 2 by decide)]
  intro z _ hz
  simp (disch := omega) only [sat_mem, Function.update_self, Function.update_of_ne] at hb hz ⊢
  exact ZFSet.mem_sUnion.mpr ⟨b, hb, hz⟩

theorem satIn_infAx {θ : Ordinal.{u}} (h : IsAdmissible θ) (v : ℕ → ZFSet.{u}) :
    SatIn (L θ) v infAx := by
  have hT := L_transitive θ
  have hω : ωZ.{u} ∈ L θ := h.omega_mem
  simp only [infAx, SatIn, sat_ex, sat_and]
  refine ⟨ωZ, hω, ⟨natZ 0, natZ_mem_L h.omega_lt 0, ?_⟩, ?_⟩
  · simp (disch := omega) only [sat_mem, Function.update_self, Function.update_of_ne]
    exact natZ_mem_ωZ 0
  · rw [sat_ball_of_ne (show (1 : ℕ) ≠ 0 by decide)]
    intro a _ ha
    simp only [Function.update_self] at ha
    rw [sat_bex_of_ne (show (2 : ℕ) ≠ 0 by decide)]
    obtain ⟨n, rfl⟩ := mem_ωZ_iff.mp ha
    refine ⟨natZ (n + 1), natZ_mem_L h.omega_lt _, ?_, ?_⟩
    · simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      exact natZ_mem_ωZ _
    · simp (disch := omega) only [sat_mem, Function.update_self, Function.update_of_ne]
      exact natZ_mem_natZ_iff.mpr (by omega)

/-! ### Δ₀-Separation -/

/-- Only the *witness* variable `y` has to be non-free in `φ`: `j` and `x` are universally
quantified in front, so free occurrences of them in `φ` are parameters, and `i` is the element
variable the schema separates by. -/
theorem satIn_sepAx {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {φ : Fm} (hφ : Fm.IsDelta0 φ)
    {i j x y : ℕ} (hyfv : y ∉ Fm.fv φ)
    (hij : i ≠ j) (hix : i ≠ x) (hiy : i ≠ y) (hjx : j ≠ x) (hjy : j ≠ y) (hxy : x ≠ y)
    (v : ℕ → ZFSet.{u}) (hv : ∀ n, v n ∈ L θ) : SatIn (L θ) v (sepAx φ i j x y) := by
  have hT := L_transitive θ
  have hP : Delta0Def (Fm.fv φ) (fun D w => Sat D w φ) :=
    ⟨φ, hφ, subset_rfl, fun _ _ _ _ => Iff.rfl⟩
  simp only [sepAx, SatIn, sat_all, sat_ex, sat_iff, sat_and, sat_mem]
  intro p hp a ha
  have hv₂ : ∀ n, (Function.update (Function.update v j p) x a) n ∈ L θ :=
    update_forall_mem (update_forall_mem hv j hp) x ha
  have main : ∀ B z : ZFSet.{u}, z ∈ L θ →
      (Sat (· ∈ L θ) (Function.update
        (Function.update (Function.update (Function.update v j p) x a) y B) i z) φ ↔
       Sat (fun _ => True)
        (Function.update (Function.update (Function.update v j p) x a) i z) φ) := by
    intro B z hz
    refine Iff.trans (sat_congr ?_) (hφ.satIn_iff_satV hT ?_)
    · intro k hk
      by_cases hki : k = i
      · subst hki; simp
      · rw [Function.update_of_ne hki, Function.update_of_ne hki,
          Function.update_of_ne (show k ≠ y from fun e => hyfv (e ▸ hk))]
    · intro k _
      exact update_forall_mem hv₂ i hz k
  have hb := sep_mem_L_of_limit hθ hP i
    (v := Function.update (Function.update v j p) x a) (fun k _ => hv₂ k) ha
  refine ⟨_, hb, ?_⟩
  intro z hz
  simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  simp only [ZFSet.mem_sep]
  exact and_congr_right fun _ => (main _ z hz).symm

/-! ### Δ₀-Collection -/

/-- Only the *witness* variable `y` has to be non-free in `φ`: `x` is universally quantified in
front, and `i`, `j` are the two variables the collection schema is about. -/
theorem satIn_collAx {θ : Ordinal.{u}} (h : IsAdmissible θ) {φ : Fm} (hφ : Fm.IsDelta0 φ)
    {i j x y : ℕ} (hyfv : y ∉ Fm.fv φ)
    (hij : i ≠ j) (hix : i ≠ x) (hiy : i ≠ y) (hjx : j ≠ x) (hjy : j ≠ y) (hxy : x ≠ y)
    (v : ℕ → ZFSet.{u}) (hv : ∀ n, v n ∈ L θ) : SatIn (L θ) v (collAx φ i j x y) := by
  have hT := L_transitive θ
  have hP : Delta0Def (Fm.fv φ) (fun D w => Sat D w φ) :=
    ⟨φ, hφ, subset_rfl, fun _ _ _ _ => Iff.rfl⟩
  simp only [collAx, SatIn, sat_all, sat_imp]
  intro a ha hant
  rw [sat_ball_of_ne hix] at hant
  simp (disch := omega) only [sat_ex, Function.update_self] at hant
  have hva : ∀ n, (Function.update v x a) n ∈ L θ := update_forall_mem hv x ha
  have hcol := h.collection (Fm.fv φ) (fun D w => Sat D w φ) hP i j hij
    (Function.update v x a) (fun k _ => hva k) a ha ?_
  · obtain ⟨b, hbL, hb⟩ := hcol
    rw [sat_ex]
    refine ⟨b, hbL, ?_⟩
    rw [sat_ball_of_ne hix]
    intro z hzL hza
    simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hza
    rw [sat_bex_of_ne hjy]
    obtain ⟨t, htb, hsat⟩ := hb z hza
    refine ⟨t, hT.subset_of_mem hbL htb, ?_, ?_⟩
    · simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      exact htb
    · refine (sat_congr ?_).mpr hsat
      intro k hk
      have hky : k ≠ y := fun e => hyfv (e ▸ hk)
      by_cases hkj : k = j
      · subst hkj; simp
      · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
        by_cases hki : k = i
        · subst hki; simp
        · rw [Function.update_of_ne hki, Function.update_of_ne hki,
            Function.update_of_ne hky]
  · intro z hz
    obtain ⟨t, htL, hsat⟩ := hant z (hT.subset_of_mem ha hz) hz
    exact ⟨t, htL, hsat⟩

/-! ### Set induction -/

/-- The auxiliary variable `i` has to be non-free in `φ`, so that `∀j (j = i → φ)` really is the
substitution `φ(i)`.  The induction variable `j` is the one `φ` is about. -/
theorem satIn_indAx {θ : Ordinal.{u}} {φ : Fm} {i j : ℕ}
    (hifv : i ∉ Fm.fv φ) (hij : i ≠ j)
    (v : ℕ → ZFSet.{u}) : SatIn (L θ) v (indAx φ i j) := by
  have hT := L_transitive θ
  simp only [indAx, SatIn, sat_all, sat_imp]
  intro H t
  induction t using ZFSet.inductionOn with
  | _ t ih =>
    intro htL
    apply H t htL
    rw [sat_ball_of_ne hij]
    intro z hzL hzt
    simp only [Function.update_self] at hzt
    intro s hsL heq
    simp (disch := omega) only [sat_eq, Function.update_self, Function.update_of_ne] at heq
    have hz' : Sat (· ∈ L θ) (Function.update v j z) φ := ih z hzt (hT.subset_of_mem htL hzt)
    refine (sat_congr ?_).mpr hz'
    intro k hk
    have hki : k ≠ i := fun e => hifv (e ▸ hk)
    by_cases hkj : k = j
    · subst hkj
      simp only [Function.update_self]
      exact heq
    · rw [Function.update_of_ne hkj, Function.update_of_ne hki, Function.update_of_ne hkj,
        Function.update_of_ne hkj]

/-! ### Soundness: every recognised axiom is true in `L θ` -/

set_option maxRecDepth 8000 in
/-- Every formula whose code is recognised by `KPAxCode` is true in `L θ` for admissible `θ`,
under every valuation with values in `L θ`. -/
theorem satIn_kpAx {θ : Ordinal.{u}} (h : IsAdmissible θ) {d : ZFSet.{u}}
    (hd : KPAxCode (L Ordinal.omega0) ωZ d) :
    ∀ φ : Fm, d = Fm.code.{u} φ → ∀ v : ℕ → ZFSet.{u}, (∀ n, v n ∈ L θ) → SatIn (L θ) v φ := by
  have hlim := h.isSuccLimit
  intro φ hcode v hv
  rcases (kpAxCode_iff d).mp hd with H | H | H | H | H |
    ⟨ψ, i, j, x, y, hψ, -, hy, hij, hix, hiy, hjx, hjy, hxy, l, χ, hχ, -, H⟩ |
    ⟨ψ, i, j, hi, hij, l, -, H⟩
  · have : φ = extAx := Fm.code_injective (hcode.symm.trans H)
    subst this; exact satIn_extAx v
  · have : φ = emptyAx := Fm.code_injective (hcode.symm.trans H)
    subst this; exact satIn_emptyAx hlim v
  · have : φ = pairAx := Fm.code_injective (hcode.symm.trans H)
    subst this; exact satIn_pairAx hlim v
  · have : φ = unionAx := Fm.code_injective (hcode.symm.trans H)
    subst this; exact satIn_unionAx hlim v
  · have : φ = infAx := Fm.code_injective (hcode.symm.trans H)
    subst this; exact satIn_infAx h v
  · have : φ = Fm.alls l χ := Fm.code_injective (hcode.symm.trans H)
    subst this
    refine satIn_alls (fun v' hv' => ?_) l v hv
    rcases hχ with rfl | rfl
    · exact satIn_sepAx hlim hψ hy hij hix hiy hjx hjy hxy v' hv'
    · exact satIn_collAx h hψ hy hij hix hiy hjx hjy hxy v' hv'
  · have : φ = Fm.alls l (indAx ψ i j) := Fm.code_injective (hcode.symm.trans H)
    subst this
    exact satIn_alls (fun v' _ => satIn_indAx hi hij v') l v hv

/-- The same, with the weaker requirement that only the *free* variables of the axiom are given
values in `L θ`. -/
theorem satIn_kpAx_of_valD {θ : Ordinal.{u}} (h : IsAdmissible θ) {d : ZFSet.{u}}
    (hd : KPAxCode (L Ordinal.omega0) ωZ d) :
    ∀ φ : Fm, d = Fm.code.{u} φ → ∀ v : ℕ → ZFSet.{u}, ValD (· ∈ L θ) (Fm.fv φ) v →
      SatIn (L θ) v φ := by
  classical
  intro φ hcode v hv
  obtain ⟨v', hv'mem, hv'eq⟩ : ∃ v' : ℕ → ZFSet.{u}, (∀ n, v' n ∈ L θ) ∧
      (∀ k ∈ Fm.fv φ, v' k = v k) := by
    refine ⟨fun n => if n ∈ Fm.fv φ then v n else ∅, ?_, ?_⟩
    · intro n
      by_cases hn : n ∈ Fm.fv φ
      · simp only [if_pos hn]; exact hv n hn
      · simp only [if_neg hn]; exact empty_mem_L_of_limit h.isSuccLimit
    · intro k hk
      simp only [if_pos hk]
  exact (sat_congr hv'eq).mp (satIn_kpAx h hd φ hcode v' hv'mem)

/-! ### Completeness: truth of the recognised axioms implies admissibility -/

/-- Conversely, if `η > ω` is a limit ordinal in which every formula recognised by `KPAxCode` is
true (under every valuation with values in `L η`), then `η` is admissible. -/
theorem isAdmissible_of_kpTrue {η : Ordinal.{u}} (homega : Ordinal.omega0 < η)
    (hlim : Order.IsSuccLimit η)
    (hall : ∀ φ : Fm, KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} φ) →
      ∀ v : ℕ → ZFSet.{u}, (∀ n, v n ∈ L η) → SatIn (L η) v φ) :
    IsAdmissible η := by
  refine ⟨homega, hlim, ?_⟩
  intro s P hP i j hij v hv a ha hcol
  have hT := L_transitive η
  have hD : GoodDom (· ∈ L η) := goodDom_mem hT (L_nonempty (Ordinal.omega0_pos.trans homega))
  obtain ⟨φ, hφΔ, hfvs, hsat⟩ := id hP
  -- a variable index above everything in sight
  obtain ⟨N, hiN, hjN, hvarsN, hsN⟩ : ∃ N : ℕ, i < N ∧ j < N ∧ (∀ k ∈ Fm.vars φ, k < N) ∧
      (∀ k ∈ s, k < N) := by
    refine ⟨Fm.bound φ + s.sup id + i + j + 1, by omega, by omega, ?_, ?_⟩
    · intro k hk; have := Fm.lt_bound hk; omega
    · intro k hk; have : k ≤ s.sup id := Finset.le_sup (f := id) hk; omega
  have hcode : KPAxCode (L Ordinal.omega0) ωZ
      (Fm.code.{u} (Fm.alls (Fm.fv (collAx φ i j N (N + 1))).toList (collAx φ i j N (N + 1)))) :=
    kpAxCode_coll hφΔ (notFree_of_vars_lt hvarsN le_rfl)
      (notFree_of_vars_lt hvarsN (by omega)) hij
      (by omega) (by omega) (by omega) (by omega) (by omega) _
      (subset_toList_toFinset _)
  -- a valuation with values in `L η` agreeing with `v` on the parameters
  obtain ⟨v', hv'mem, hv'eq⟩ : ∃ v' : ℕ → ZFSet.{u}, (∀ n, v' n ∈ L η) ∧
      (∀ k ∈ s, k ≠ i → k ≠ j → v' k = v k) := by
    classical
    refine ⟨fun n => if n ∈ (s.erase i).erase j then v n else ∅, ?_, ?_⟩
    · intro n
      by_cases hn : n ∈ (s.erase i).erase j
      · simp only [if_pos hn]; exact hv n hn
      · simp only [if_neg hn]; exact empty_mem_L_of_limit hlim
    · intro k hk hki hkj
      simp only [if_pos (Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hk⟩⟩)]
  have hcongr : ∀ (u : ℕ → ZFSet.{u}) (z t : ZFSet.{u}),
      (∀ k ∈ Fm.fv φ, k ≠ i → k ≠ j → u k = v k) →
      (Sat (· ∈ L η) (Function.update (Function.update u i z) j t) φ ↔
       Sat (· ∈ L η) (Function.update (Function.update v i z) j t) φ) := by
    intro u z t hu
    apply sat_congr
    intro k hk
    by_cases hkj : k = j
    · subst hkj; simp
    · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
      by_cases hki : k = i
      · subst hki; simp
      · rw [Function.update_of_ne hki, Function.update_of_ne hki]
        exact hu k hk hki hkj
  have hvalv : ∀ z t : ZFSet.{u}, z ∈ L η → t ∈ L η →
      ValD (· ∈ L η) s (Function.update (Function.update v i z) j t) := by
    intro z t hz ht k hk
    by_cases hkj : k = j
    · subst hkj; simpa
    · rw [Function.update_of_ne hkj]
      by_cases hki : k = i
      · subst hki; simpa
      · rw [Function.update_of_ne hki]
        exact hv k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hk⟩⟩)
  have hsatColl := sat_of_alls hv'mem (hall _ hcode v' hv'mem)
  simp only [collAx, sat_all, sat_imp] at hsatColl
  have hant : Sat (· ∈ L η) (Function.update v' N a) (Fm.ball i N (Fm.ex j φ)) := by
    rw [sat_ball_of_ne (show i ≠ N by omega)]
    intro z hzL hza
    simp only [Function.update_self] at hza
    rw [sat_ex]
    obtain ⟨t, htL, hPt⟩ := hcol z hza
    refine ⟨t, htL, ?_⟩
    refine (hcongr (Function.update v' N a) z t ?_).mpr
      ((hsat (· ∈ L η) _ hD (hvalv z t hzL htL)).mpr hPt)
    intro k hk hki hkj
    have hkN : k < N := hsN k (hfvs hk)
    rw [Function.update_of_ne (by omega : k ≠ N)]
    exact hv'eq k (hfvs hk) hki hkj
  obtain ⟨b, hbL, hb⟩ := sat_ex.mp (hsatColl a ha hant)
  refine ⟨b, hbL, ?_⟩
  rw [sat_ball_of_ne (show i ≠ N by omega)] at hb
  intro z hza
  have hzL : z ∈ L η := hT.subset_of_mem ha hza
  have h3 := hb z hzL (by
    simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    exact hza)
  rw [sat_bex_of_ne (show j ≠ N + 1 by omega)] at h3
  obtain ⟨t, htL, htb, hst⟩ := h3
  simp (disch := omega) only [Function.update_of_ne, Function.update_self] at htb
  refine ⟨t, htb, ?_⟩
  refine (hsat (· ∈ L η) _ hD (hvalv z t hzL htL)).mp ?_
  refine (hcongr (Function.update (Function.update v' N a) (N + 1) b) z t ?_).mp hst
  intro k hk hki hkj
  have hkN : k < N := hsN k (hfvs hk)
  rw [Function.update_of_ne (by omega : k ≠ N + 1), Function.update_of_ne (by omega : k ≠ N)]
  exact hv'eq k (hfvs hk) hki hkj

end BM4.ST
