import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_936_aux

theorem sgn_ind {a b : Bool} :
    ((if a ≠ b then (1 : ℚ) else 0)) =
      (1 - (if a then (-1 : ℚ) else 1) * (if b then (-1 : ℚ) else 1)) / 2 := by
  cases a <;> cases b <;> norm_num

theorem sgn_sq (a : Bool) : (if a then (-1 : ℚ) else 1) * (if a then (-1 : ℚ) else 1) = 1 := by
  cases a <;> norm_num

theorem sgn_opp {a b : Bool} (h : a ≠ b) : (if b then (-1 : ℚ) else 1) = -(if a then (-1 : ℚ) else 1) := by
  cases a <;> cases b <;> simp_all

theorem cnt_eq {k : ℕ} (g : Fin k → Bool) :
    (∑ y : Fin k, (if g y = true then (1 : ℚ) else 0)) = ((Finset.univ.filter (fun y => g y = true)).card : ℚ) := by
  rw [Finset.sum_boole]

theorem ind_sum {n k : ℕ} (f : Fin n → Fin k → Bool) (i j : Fin n) :
    (∑ y : Fin k, (if f i y ≠ f j y then (1 : ℚ) else 0)) =
      (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) := by
  rw [Finset.sum_boole]

theorem diff_pos {n k : ℕ} (f : Fin n → Fin k → Bool) (hf : ∀ i j, i ≠ j → ∃ y, f i y ≠ f j y)
    (i j : Fin n) (hij : i ≠ j) :
    (0 : ℚ) < (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) := by
  obtain ⟨y, hy⟩ := hf i j hij
  have : 0 < ((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card :=
    Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
  exact_mod_cast this

theorem diff_symm {n k : ℕ} (f : Fin n → Fin k → Bool) (i j : Fin n) :
    ((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card =
      ((Finset.univ : Finset (Fin k)).filter (fun y => f j y ≠ f i y)).card := by
  congr 1
  ext y
  simp [ne_comm]

theorem row_sum {n k : ℕ} (f : Fin n → Fin k → Bool) (hf : ∀ i j, i ≠ j → ∃ y, f i y ≠ f j y) (i j : Fin n) :
    (∑ y : Fin k, (if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0)) =
      if j = i then 0 else 1 := by
  have e : ∀ y : Fin k, (if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) =
      (if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ)) := by
    intro y; split_ifs <;> simp
  simp only [e]
  rw [← Finset.sum_mul, ind_sum]
  by_cases hji : j = i
  · subst hji; simp
  · rw [if_neg hji]
    have := diff_pos f hf i j (Ne.symm hji)
    field_simp


theorem p1 {n k : ℕ} (hn : 2 ≤ n) (f : Fin n → Fin k → Bool) (i : Fin n) (y : Fin k) :
    0 ≤ (∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) / ((n : ℚ) - 1) := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity
  · have : (2 : ℚ) ≤ n := by exact_mod_cast hn
    linarith

theorem cnt_ne {n : ℕ} (i : Fin n) : (∑ j : Fin n, if j = i then (0 : ℚ) else 1) = (n : ℚ) - 1 := by
  have h1 : (∑ j : Fin n, if j = i then (0 : ℚ) else 1) = ∑ j : Fin n, (1 - if j = i then (1 : ℚ) else 0) := by
    apply Finset.sum_congr rfl; intro j _; split_ifs <;> norm_num
  rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

theorem p2 {n k : ℕ} (hn : 2 ≤ n) (f : Fin n → Fin k → Bool) (hf : ∀ i j, i ≠ j → ∃ y, f i y ≠ f j y) (i : Fin n) :
    (∑ y : Fin k, (∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) / ((n : ℚ) - 1)) = 1 := by
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [row_sum f hf i]
  rw [cnt_ne]
  have : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hne : (n : ℚ) - 1 ≠ 0 := by linarith
  exact div_self hne

theorem p3 {n k : ℕ} (f : Fin n → Fin k → Bool) (y : Fin k) :
    (∑ i : Fin n, (∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) / ((n : ℚ) - 1) *
      (if f i y = true then (-1 : ℚ) else 1)) = 0 := by
  have e : ∀ i : Fin n, (∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) / ((n : ℚ) - 1) *
      (if f i y = true then (-1 : ℚ) else 1) =
      (∑ j : Fin n, (if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) *
        (if f i y = true then (-1 : ℚ) else 1)) / ((n : ℚ) - 1) := by
    intro i
    rw [div_mul_eq_mul_div, Finset.sum_mul]
  simp only [e]
  rw [← Finset.sum_div]
  have anti : ∀ i j : Fin n, (if f j y ≠ f i y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f j y ≠ f i y)).card : ℚ) else 0) *
      (if f j y = true then (-1 : ℚ) else 1) =
      -((if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) *
      (if f i y = true then (-1 : ℚ) else 1)) := by
    intro i j
    by_cases h : f i y = f j y
    · simp [h]
    · rw [if_pos (Ne.symm h), if_pos h, diff_symm f j i, sgn_opp h]
      ring
  have hS : (∑ i : Fin n, ∑ j : Fin n, (if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) *
        (if f i y = true then (-1 : ℚ) else 1)) = 0 := by
    set t : Fin n → Fin n → ℚ := fun a b => (if f a y ≠ f b y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f a y ≠ f b y)).card : ℚ) else 0) *
        (if f a y = true then (-1 : ℚ) else 1) with ht
    have h2 : (∑ a : Fin n, ∑ b : Fin n, t a b) = -(∑ a : Fin n, ∑ b : Fin n, t a b) := by
      calc (∑ a : Fin n, ∑ b : Fin n, t a b) = ∑ b : Fin n, ∑ a : Fin n, t a b := Finset.sum_comm
        _ = ∑ b : Fin n, ∑ a : Fin n, -(t b a) := by
          apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro a _
          exact anti b a
        _ = -(∑ a : Fin n, ∑ b : Fin n, t a b) := by
          simp only [Finset.sum_neg_distrib]
    linarith
  rw [hS, zero_div]

theorem p4_ind_sum {n k : ℕ} (f : Fin n → Fin k → Bool) (i : Fin n) (y : Fin k) :
    (∑ j : Fin n, (if f i y ≠ f j y then (1 : ℚ) else 0)) =
      ((n : ℚ) - (if f i y = true then (-1 : ℚ) else 1) * ∑ j : Fin n, (if f j y = true then (-1 : ℚ) else 1)) / 2 := by
  have e : ∀ j : Fin n, (if f i y ≠ f j y then (1 : ℚ) else 0) =
      (1 - (if f i y = true then (-1 : ℚ) else 1) * (if f j y = true then (-1 : ℚ) else 1)) / 2 := fun j => sgn_ind
  simp only [e]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

theorem p4_ident {n k : ℕ} (hk : 0 < k) (f : Fin n → Fin k → Bool) (i : Fin n) (y : Fin k) :
    (∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) - ((n : ℚ) - 1) / k =
      (∑ j : Fin n, (if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) - 2 / k)) -
        ((if f i y = true then (-1 : ℚ) else 1) * (∑ j : Fin n, (if f j y = true then (-1 : ℚ) else 1)) - 1) / k := by
  have e1 : ∀ j : Fin n, (if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) =
      (if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ)) := by
    intro j; split_ifs <;> simp
  have e2 : ∀ j : Fin n, (if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) - 2 / k) =
      (if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ)) -
        (2 / k) * (if f i y ≠ f j y then (1 : ℚ) else 0) := by
    intro j; ring
  simp only [e1, e2]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, p4_ind_sum]
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp
  ring

theorem p4_pt {n k : ℕ} (hk : 0 < k) (f : Fin n → Fin k → Bool) (i : Fin n) (y : Fin k) :
    |(∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) - ((n : ℚ) - 1) / k| ≤
      (∑ j : Fin n, |(if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) - 2 / k)|) +
        (|∑ j : Fin n, (if f j y = true then (-1 : ℚ) else 1)| + 1) / k := by
  rw [p4_ident hk]
  have hkpos : (0 : ℚ) < k := by exact_mod_cast hk
  have hs : |(if f i y = true then (-1 : ℚ) else 1)| = 1 := by split_ifs <;> norm_num
  calc _ ≤ |∑ j : Fin n, (if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) - 2 / k)| +
        |((if f i y = true then (-1 : ℚ) else 1) * (∑ j : Fin n, (if f j y = true then (-1 : ℚ) else 1)) - 1) / k| := abs_sub _ _
    _ ≤ _ := by
      apply add_le_add (Finset.abs_sum_le_sum_abs _ _)
      rw [abs_div, abs_of_pos hkpos]
      apply div_le_div_of_nonneg_right _ hkpos.le
      calc _ ≤ |(if f i y = true then (-1 : ℚ) else 1) * (∑ j : Fin n, (if f j y = true then (-1 : ℚ) else 1))| + |(1 : ℚ)| := abs_sub _ _
        _ = _ := by rw [abs_mul, hs, one_mul, abs_one]

theorem p4_col {n k : ℕ} (hk : 0 < k) (f : Fin n → Fin k → Bool) (hf : ∀ i j, i ≠ j → ∃ y, f i y ≠ f j y) (i j : Fin n) :
    (∑ y : Fin k, |(if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) - 2 / k)|) +
      (if j = i then (1 : ℚ) else 0) =
      |(∑ y : Fin k, (if f i y = true then (-1 : ℚ) else 1) * (if f j y = true then (-1 : ℚ) else 1)) / k| := by
  have hkpos : (0 : ℚ) < k := by exact_mod_cast hk
  have e1 : ∀ y : Fin k, |(if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) - 2 / k)| =
      (if f i y ≠ f j y then (1 : ℚ) else 0) * |1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) - 2 / k| := by
    intro y; rw [abs_mul]; split_ifs <;> simp
  have e2 : ∀ y : Fin k, (if f i y = true then (-1 : ℚ) else 1) * (if f j y = true then (-1 : ℚ) else 1) =
      1 - 2 * (if f i y ≠ f j y then (1 : ℚ) else 0) := by
    intro y; rw [sgn_ind]; ring
  simp only [e1, e2]
  rw [← Finset.sum_mul, ind_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ind_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  by_cases hji : j = i
  · subst hji
    simp [hkpos.ne']
  · rw [if_neg hji]
    have hD := diff_pos f hf i j (Ne.symm hji)
    rw [← abs_of_pos hD, ← abs_mul, abs_of_pos hD, add_zero]
    congr 1
    field_simp

theorem p4 {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k) (f : Fin n → Fin k → Bool) (hf : ∀ i j, i ≠ j → ∃ y, f i y ≠ f j y) (i : Fin n) :
    ((n : ℚ) - 1) * (∑ y : Fin k, |(∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) / ((n : ℚ) - 1) - 1 / k|) ≤
      (n : ℚ) * ((∑ y : Fin k, |(∑ j : Fin n, (if f j y = true then (-1 : ℚ) else 1)) / n|) / k) +
        ∑ j : Fin n, |(∑ y : Fin k, (if f i y = true then (-1 : ℚ) else 1) * (if f j y = true then (-1 : ℚ) else 1)) / k| := by
  have hn' : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  have hnpos : (0 : ℚ) < n := by linarith
  have hkpos : (0 : ℚ) < k := by exact_mod_cast hk
  have e1 : ∀ y : Fin k, ((n : ℚ) - 1) * |(∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) / ((n : ℚ) - 1) - 1 / k| =
      |(∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) else 0) - ((n : ℚ) - 1) / k| := by
    intro y
    rw [← abs_of_pos hn1, ← abs_mul, abs_of_pos hn1]
    congr 1
    field_simp
  rw [Finset.mul_sum]
  simp only [e1]
  have e2 : (n : ℚ) * ((∑ y : Fin k, |(∑ j : Fin n, (if f j y = true then (-1 : ℚ) else 1)) / n|) / k) =
      (∑ y : Fin k, |∑ j : Fin n, (if f j y = true then (-1 : ℚ) else 1)|) / k := by
    simp only [abs_div, abs_of_pos hnpos]
    rw [← Finset.sum_div]
    field_simp
  rw [e2]
  have e3 : (∑ j : Fin n, |(∑ y : Fin k, (if f i y = true then (-1 : ℚ) else 1) * (if f j y = true then (-1 : ℚ) else 1)) / k|) =
      (∑ j : Fin n, ∑ y : Fin k, |(if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) - 2 / k)|) + 1 := by
    simp only [← p4_col hk f hf i]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  rw [e3]
  calc _ ≤ ∑ y : Fin k, ((∑ j : Fin n, |(if f i y ≠ f j y then (1 : ℚ) else 0) * (1 / (((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card : ℚ) - 2 / k)|) +
        (|∑ j : Fin n, (if f j y = true then (-1 : ℚ) else 1)| + 1) / k) := Finset.sum_le_sum (fun y _ => p4_pt hk f i y)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_div, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
      ring

end PEqualNP.Outside.L_lib_936_aux

theorem PEqualNP.Outside.L_lib_936 : (∀ (n k : Nat), 2 ≤ n → 0 < k → ∀ f : Fin n → Fin k → Bool,
  (∀ i j, i ≠ j → ∃ y, f i y ≠ f j y) →
  let sign := fun (i : Fin n) (y : Fin k) => if f i y then (-1 : ℚ) else 1
  let diff := fun (i j : Fin n) =>
    ((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card
  let P := fun (i : Fin n) (y : Fin k) =>
    (∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) / ((n : ℚ)-1)
  let corr := fun (i j : Fin n) => (∑ y : Fin k, sign i y * sign j y) / (k : ℚ)
  let silent := (∑ y : Fin k, |(∑ j : Fin n, sign j y) / (n : ℚ)|) / (k : ℚ)
  (∀ i y, 0 ≤ P i y) ∧ (∀ i, (∑ y : Fin k, P i y) = 1) ∧
  (∀ y, (∑ i : Fin n, P i y * sign i y) = 0) ∧
  ∀ i, ((n : ℚ)-1) * (∑ y : Fin k, |P i y - 1/(k : ℚ)|) ≤
    (n : ℚ)*silent + ∑ j : Fin n, |corr i j|) := by
  intro n k hn hk f hf
  dsimp only
  exact ⟨fun i y => PEqualNP.Outside.L_lib_936_aux.p1 hn f i y,
    fun i => PEqualNP.Outside.L_lib_936_aux.p2 hn f hf i,
    fun y => PEqualNP.Outside.L_lib_936_aux.p3 f y,
    fun i => PEqualNP.Outside.L_lib_936_aux.p4 hn hk f hf i⟩
