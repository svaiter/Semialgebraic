import TauCeti.Geometry.RealAlgebraic.CAD.Existence
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image

/-!
# Fibrewise least upper bounds of semialgebraic families (plan id G3)

This file provides:

* `Semialgebraic.isSemialgebraic_setOf_exists_real`, `Semialgebraic.isSemialgebraic_setOf_forall_real` :
  quantification over one extra real coordinate (`Sum.inr ()`) preserves semialgebraicity over `ℝ`
  (TauCeti's `setOf_exists_sumElim` / `setOf_forall_sumElim` with `τ := Unit`, written with `u : ℝ`).
* `Semialgebraic.isSemialgebraic_setOf_le_coord`, `Semialgebraic.isSemialgebraic_setOf_lt_coord` :
  `{x | x i ≤ x j}` and `{x | x i < x j}` are semialgebraic.
* `Semialgebraic.isLUB_iff_forall_lt_exists` : for `A : Set ℝ`,
  `IsLUB A s ↔ (∀ u ∈ A, u ≤ s) ∧ ∀ s' < s, ∃ u ∈ A, s' < u`.
* `Semialgebraic.isSemialgebraic_setOf_isLUB` (G3) : the graph of the fibrewise least upper bound of a semialgebraic
  family of subsets of `ℝ` is semialgebraic (no finiteness of the parameter type).
* `Semialgebraic.isSemialgebraic_setOf_isLUB_fin_two` (G3 in the plane; coordinate `0` = value, `1` = parameter).

No deviation from the brief; the statements of G3 are exactly as in the plan.
-/

open MvPolynomial

namespace Semialgebraic

/-- Existential quantification over one real coordinate preserves semialgebraicity. -/
theorem isSemialgebraic_setOf_exists_real {σ : Type*} {S : Set (σ ⊕ Unit → ℝ)}
    (hS : TauCeti.IsSemialgebraic S) :
    TauCeti.IsSemialgebraic {x : σ → ℝ | ∃ u : ℝ, Sum.elim x (fun _ => u) ∈ S} := by
  have h := hS.setOf_exists_sumElim (τ := Unit)
  convert h using 1
  ext x
  simp only [Set.mem_ofPred]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨fun _ => u, hu⟩
  · rintro ⟨y, hy⟩
    -- `y` is determined by its value at `()`
    have hy' : y = fun _ => y () := funext fun _ => rfl
    exact ⟨y (), hy' ▸ hy⟩

/-- Universal quantification over one real coordinate preserves semialgebraicity. -/
theorem isSemialgebraic_setOf_forall_real {σ : Type*} {S : Set (σ ⊕ Unit → ℝ)}
    (hS : TauCeti.IsSemialgebraic S) :
    TauCeti.IsSemialgebraic {x : σ → ℝ | ∀ u : ℝ, Sum.elim x (fun _ => u) ∈ S} := by
  have h := hS.setOf_forall_sumElim (τ := Unit)
  convert h using 1
  ext x
  simp only [Set.mem_ofPred]
  constructor
  · intro hx y
    -- `y` is determined by its value at `()`
    have hy' : y = fun _ => y () := funext fun _ => rfl
    exact hy' ▸ hx (y ())
  · intro hx u
    exact hx fun _ => u

/-- A coordinate inequality `x i ≤ x j` defines a semialgebraic set. -/
theorem isSemialgebraic_setOf_le_coord {ι : Type*} (i j : ι) :
    TauCeti.IsSemialgebraic {x : ι → ℝ | x i ≤ x j} := by
  simpa only [eval_X] using TauCeti.isSemialgebraic_eval_le (X i : MvPolynomial ι ℝ) (X j)

/-- A strict coordinate inequality `x i < x j` defines a semialgebraic set. -/
theorem isSemialgebraic_setOf_lt_coord {ι : Type*} (i j : ι) :
    TauCeti.IsSemialgebraic {x : ι → ℝ | x i < x j} := by
  simpa only [eval_X] using TauCeti.isSemialgebraic_eval_lt (X i : MvPolynomial ι ℝ) (X j)

/-- Least upper bounds in `ℝ` in first-order form. -/
theorem isLUB_iff_forall_lt_exists {A : Set ℝ} {s : ℝ} :
    IsLUB A s ↔ (∀ u ∈ A, u ≤ s) ∧ ∀ s' < s, ∃ u ∈ A, s' < u := by
  constructor
  · intro h
    refine ⟨fun u hu => h.1 hu, fun s' hs' => ?_⟩
    obtain ⟨u, hu, hsu, -⟩ := h.exists_between hs'
    exact ⟨u, hu, hsu⟩
  · rintro ⟨hub, hlt⟩
    refine ⟨fun u hu => hub u hu, fun b hb => ?_⟩
    -- if `b < s`, some element of `A` exceeds the upper bound `b`
    by_contra hbs
    obtain ⟨u, hu, hbu⟩ := hlt b (lt_of_not_ge hbs)
    exact absurd (hb hu) (not_le_of_gt hbu)

/-- G3. The graph of the fibrewise least upper bound of a semialgebraic family of subsets of `ℝ` is
semialgebraic. `Sum.inl` coordinates are the parameters, `Sum.inr ()` is the value. No finiteness of `σ`. -/
theorem isSemialgebraic_setOf_isLUB {σ : Type*} {E : Set (σ ⊕ Unit → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    TauCeti.IsSemialgebraic
      {z : σ ⊕ Unit → ℝ | IsLUB {u : ℝ | Sum.elim (z ∘ Sum.inl) (fun _ => u) ∈ E} (z (Sum.inr ()))} := by
  -- Pullback of `E` to `(σ ⊕ Unit) ⊕ Unit`: parameters `inl (inl ·)`, value `inr ()`.
  have hE₁ : TauCeti.IsSemialgebraic
      {w : (σ ⊕ Unit) ⊕ Unit → ℝ | Sum.elim (fun i => w (Sum.inl (Sum.inl i))) (fun _ => w (Sum.inr ())) ∈ E} := by
    convert hE.preimage_comp (Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr ()) :
      σ ⊕ Unit → (σ ⊕ Unit) ⊕ Unit) using 1
    ext w
    exact Iff.of_eq (congrArg (· ∈ E) (funext fun i => by cases i <;> rfl))
  -- Pullback of `E` to `((σ ⊕ Unit) ⊕ Unit) ⊕ Unit`: parameters `inl (inl (inl ·))`, value `inr ()`.
  have hE₂ : TauCeti.IsSemialgebraic
      {v : ((σ ⊕ Unit) ⊕ Unit) ⊕ Unit → ℝ |
        Sum.elim (fun i => v (Sum.inl (Sum.inl (Sum.inl i)))) (fun _ => v (Sum.inr ())) ∈ E} := by
    convert hE.preimage_comp (Sum.elim (fun i => Sum.inl (Sum.inl (Sum.inl i))) (fun _ => Sum.inr ()) :
      σ ⊕ Unit → ((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) using 1
    ext v
    exact Iff.of_eq (congrArg (· ∈ E) (funext fun i => by cases i <;> rfl))
  -- Upper bound condition: `∀ u, u ∈ fibre → u ≤ value`.
  have hUB : TauCeti.IsSemialgebraic
      {z : σ ⊕ Unit → ℝ | ∀ u : ℝ, Sum.elim (z ∘ Sum.inl) (fun _ => u) ∈ E → u ≤ z (Sum.inr ())} := by
    have hS : TauCeti.IsSemialgebraic
        ({w : (σ ⊕ Unit) ⊕ Unit → ℝ |
            Sum.elim (fun i => w (Sum.inl (Sum.inl i))) (fun _ => w (Sum.inr ())) ∈ E}ᶜ ∪
          {w | w (Sum.inr ()) ≤ w (Sum.inl (Sum.inr ()))}) :=
      hE₁.compl.union (isSemialgebraic_setOf_le_coord _ _)
    convert isSemialgebraic_setOf_forall_real hS using 1
    ext z
    simp only [Set.mem_ofPred, Set.mem_union, Set.mem_compl_iff, Sum.elim_inl, Sum.elim_inr,
      Function.comp_def, imp_iff_not_or]
  -- Least condition, inner part: `∃ u, u ∈ fibre ∧ s' < u`, with `s'` at `inl (inr ())`.
  have hEx : TauCeti.IsSemialgebraic
      {w : (σ ⊕ Unit) ⊕ Unit → ℝ | ∃ u : ℝ,
        Sum.elim (fun i => w (Sum.inl (Sum.inl i))) (fun _ => u) ∈ E ∧ w (Sum.inr ()) < u} := by
    have hT := hE₂.inter (isSemialgebraic_setOf_lt_coord (Sum.inl (Sum.inr ())) (Sum.inr ()))
    convert isSemialgebraic_setOf_exists_real hT using 1
    ext w
    simp only [Set.mem_ofPred, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr]
  -- Least condition: `∀ s', s' < value → ∃ u, u ∈ fibre ∧ s' < u`.
  have hLeast : TauCeti.IsSemialgebraic
      {z : σ ⊕ Unit → ℝ | ∀ s' : ℝ, s' < z (Sum.inr ()) →
        ∃ u : ℝ, Sum.elim (z ∘ Sum.inl) (fun _ => u) ∈ E ∧ s' < u} := by
    have hS := (isSemialgebraic_setOf_lt_coord (ι := (σ ⊕ Unit) ⊕ Unit)
      (Sum.inr ()) (Sum.inl (Sum.inr ()))).compl.union hEx
    convert isSemialgebraic_setOf_forall_real hS using 1
    ext z
    simp only [Set.mem_ofPred, Set.mem_union, Set.mem_compl_iff, Sum.elim_inl, Sum.elim_inr,
      Function.comp_def, imp_iff_not_or]
  -- Combine both halves.
  convert hUB.inter hLeast using 1
  ext z
  simp only [Set.mem_ofPred, Set.mem_inter_iff, isLUB_iff_forall_lt_exists]

/-- G3 in the plane: coordinate `0` is the value, coordinate `1` is the parameter. -/
theorem isSemialgebraic_setOf_isLUB_fin_two {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    TauCeti.IsSemialgebraic {z : Fin 2 → ℝ | IsLUB {u : ℝ | ![u, z 1] ∈ E} (z 0)} := by
  -- Transport `E` to `Unit ⊕ Unit`: parameter `inl ()`, value `inr ()`.
  set g : Fin 2 → Unit ⊕ Unit := ![Sum.inr (), Sum.inl ()] with hg
  have hE' : TauCeti.IsSemialgebraic ((fun w : Unit ⊕ Unit → ℝ => w ∘ g) ⁻¹' E) := hE.preimage_comp g
  have hG := isSemialgebraic_setOf_isLUB hE'
  -- Pull the result back along `h : Unit ⊕ Unit → Fin 2`, `inl () ↦ 1`, `inr () ↦ 0`.
  convert hG.preimage_comp (Sum.elim (fun _ => (1 : Fin 2)) (fun _ => (0 : Fin 2))) using 1
  ext z
  simp only [Set.mem_ofPred, Set.mem_preimage]
  -- the two fibres coincide
  have hfib : ∀ u : ℝ, (Sum.elim ((z ∘ Sum.elim (fun _ : Unit => (1 : Fin 2)) (fun _ : Unit => (0 : Fin 2))) ∘
      Sum.inl) (fun _ : Unit => u)) ∘ g = ![u, z 1] := by
    intro u
    funext i
    fin_cases i <;> simp [hg]
  simp only [hfib, Function.comp_apply, Sum.elim_inr]
