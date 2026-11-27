import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_605_aux

theorem cover_of_inj (m r : ℕ) (label : Fin m → Fin (m + 1) → (Fin r → Bool))
    (hinj : ∀ i, Function.Injective (label i)) (x : Fin m → (Fin r → Bool)) :
    ∃ a, ∀ i, x i ≠ label i a := by
  by_contra hcon
  have h : ∀ a, ∃ i, x i = label i a := by
    intro a
    by_contra ha
    exact hcon ⟨a, fun i hi => ha ⟨i, hi⟩⟩
  choose f hf using h
  have finj : Function.Injective f := by
    intro a a' haa
    apply hinj (f a)
    rw [← hf a, haa]
    exact hf a'
  have hcard := Fintype.card_le_of_injective f finj
  simp at hcard

theorem inj_of_cover (m r : ℕ) (label : Fin m → Fin (m + 1) → (Fin r → Bool))
    (hcov : ∀ x : Fin m → (Fin r → Bool), ∃ a, ∀ i, x i ≠ label i a) (i : Fin m) :
    Function.Injective (label i) := by
  intro a a' hlab
  by_contra hne
  obtain ⟨j0, hj0⟩ := Fin.exists_succAbove_eq hne
  obtain ⟨c, hc⟩ := hcov (fun j => label j (a'.succAbove (Equiv.swap i j0 j)))
  by_cases hca : c = a'
  · apply hc i
    show label i (a'.succAbove (Equiv.swap i j0 i)) = label i c
    rw [Equiv.swap_apply_left, hj0, hca, hlab]
  · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hca
    apply hc (Equiv.swap i j0 z)
    show label (Equiv.swap i j0 z) (a'.succAbove (Equiv.swap i j0 (Equiv.swap i j0 z)))
      = label (Equiv.swap i j0 z) c
    rw [Equiv.swap_apply_self, hz]

theorem menu (m r : ℕ) (label : Fin m → Fin (m + 1) → (Fin r → Bool))
    (hinj : ∀ i, Function.Injective (label i)) (b : Fin (m + 1)) (flags : Fin m → Bool)
    (v : Fin (m + 1)) :
    (∀ i, label i (if flags i then b else b.succAbove i) ≠ label i v) ↔
      (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = b.succAbove j) := by
  have key : (∀ i, label i (if flags i then b else b.succAbove i) ≠ label i v) ↔
      ∀ i, (if flags i then b else b.succAbove i) ≠ v :=
    forall_congr' (fun i => (hinj i).ne_iff)
  rw [key]
  by_cases hv : v = b
  · subst hv
    constructor
    · intro h
      left
      refine ⟨rfl, fun j => ?_⟩
      by_contra hj
      have hj' : flags j = true := by simpa using hj
      have hjv := h j
      rw [hj'] at hjv
      exact hjv (by simp)
    · rintro (⟨_, hall⟩ | ⟨j, _, hj⟩)
      · intro i
        rw [hall i]
        simp
      · exact absurd hj.symm (Fin.succAbove_ne v j)
  · obtain ⟨j0, hj0⟩ := Fin.exists_succAbove_eq hv
    constructor
    · intro h
      right
      refine ⟨j0, ?_, hj0.symm⟩
      by_contra hf
      have hf' : flags j0 = false := by simpa using hf
      have hjv := h j0
      rw [hf'] at hjv
      exact hjv (by simpa using hj0)
    · rintro (⟨hvb, _⟩ | ⟨j, hj, hvj⟩)
      · exact absurd hvb hv
      · intro i
        by_cases hi : flags i = true
        · rw [hi]
          intro hbv
          exact hv (by simpa using hbv.symm)
        · have hi' : flags i = false := by simpa using hi
          rw [hi']
          intro hiv
          have hiv' : b.succAbove i = v := by simpa using hiv
          have hij : i = j := Fin.succAbove_right_injective (hiv'.trans hvj)
          rw [hij, hj] at hi'
          exact absurd hi' (by simp)

end PEqualNP.Outside.L_lib_605_aux

theorem PEqualNP.Outside.L_lib_605 : (∀ (m r : Nat),
  let A := Fin (m+1)
  let W := Fin r → Bool
  ∀ label : Fin m → A → W,
    let ok := fun (x : Fin m → W) (a : A) => ∀ i, x i ≠ label i a
    let covers := ∀ x, ∃ a, ok x a
    (covers ↔ ∀ i, Function.Injective (label i)) ∧
    (covers → ∀ b : A, ∃ order : Fin m → A,
      Function.Injective order ∧ (∀ i, order i ≠ b) ∧
      ∀ (flags : Fin m → Bool) (v : A),
        ok (fun pos => label pos (if flags pos then b else order pos)) v ↔
          (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = order j))) := by
  intro m r
  dsimp only
  intro label
  refine ⟨⟨fun hcov i => PEqualNP.Outside.L_lib_605_aux.inj_of_cover m r label hcov i,
    fun hinj x => PEqualNP.Outside.L_lib_605_aux.cover_of_inj m r label hinj x⟩, ?_⟩
  intro hcov b
  have hinj := fun i => PEqualNP.Outside.L_lib_605_aux.inj_of_cover m r label hcov i
  exact ⟨b.succAbove, Fin.succAbove_right_injective, fun i => Fin.succAbove_ne b i,
    fun flags v => PEqualNP.Outside.L_lib_605_aux.menu m r label hinj b flags v⟩
