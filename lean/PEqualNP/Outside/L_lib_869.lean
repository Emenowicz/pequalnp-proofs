import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_869_aux

def Pre (m : ℕ) (len : Fin m → ℕ) (j : ℕ) :
    Submodule (ZMod 2) ((i : Fin m) → Fin (len i) → ZMod 2) :=
  { carrier := {x | ∀ i : Fin m, j ≤ i.val → x i = 0}
    zero_mem' := fun i _ => rfl
    smul_mem' := fun c x hx i hi => by simp [hx i hi], add_mem' := fun {x y} hx hy i hi => by simp [hx i hi, hy i hi] }

theorem mem_Pre {m : ℕ} {len : Fin m → ℕ} {j : ℕ} {x : (i : Fin m) → Fin (len i) → ZMod 2} :
    x ∈ Pre m len j ↔ ∀ i : Fin m, j ≤ i.val → x i = 0 :=
  Iff.rfl

def massAt {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ) (S : Finset (Fin s → ZMod 2))
    (c : Fin s → ZMod 2) : ℕ :=
  ∑ x : ((i : Fin m) → Fin (len i) → ZMod 2), if P x + c ∈ S then ∏ i : Fin m, a i (x i) else 0

open Classical

theorem dm_mono {m s : ℕ} {len : Fin m → ℕ}
    (R : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ) (S T : Finset (Fin s → ZMod 2))
    (c d : Fin s → ZMod 2) (h : ∀ y, y + c ∈ S → y + d ∈ T) :
    massAt R a S c ≤ massAt R a T d := by
  unfold massAt
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : R x + c ∈ S
  · simp [hx, h _ hx]
  · simp [hx]

theorem dm_best {α : Type*} [Fintype α] (f : Finset α → ℕ) (k : ℕ) :
    ∃ T : Finset α, T.card ≤ k ∧ ∀ T' : Finset α, T'.card ≤ k → f T' ≤ f T := by
  classical
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Finset α)).filter (fun T => T.card ≤ k)) f ⟨∅, by simp⟩
  exact ⟨T, (Finset.mem_filter.mp hT).2, fun T' h => hmax T' (by simp [h])⟩

theorem dm_term {m s : ℕ} {len : Fin m → ℕ}
    (R : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ) (i : Fin m) (S : Finset (Fin s → ZMod 2))
    (c : Fin s → ZMod 2) (v : Fin (len i) → ZMod 2) :
    a i v * massAt R (Function.update a i (fun w => if w = 0 then 1 else 0)) S
      (c + R (Pi.single i v)) =
    ∑ x : ((i : Fin m) → Fin (len i) → ZMod 2),
      if x i = v then (if R x + c ∈ S then ∏ k, a k (x k) else 0) else 0 := by
  unfold massAt
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (Pi.single i v : (i : Fin m) → Fin (len i) → ZMod 2))
    _ _ fun x => ?_
  dsimp only [Equiv.coe_addRight]
  by_cases hx : x i = 0
  · have e1 : (x + (Pi.single i v : (i : Fin m) → Fin (len i) → ZMod 2)) i = v := by simp [hx]
    have e2 : R (x + Pi.single i v) + c = R x + (c + R (Pi.single i v)) := by
      rw [map_add]; abel
    rw [e2]
    simp only [e1, ite_true]
    split_ifs
    · rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i, e1]
      have e3 : ∏ k ∈ ({i} : Finset (Fin m))ᶜ, a k ((x + (Pi.single i v : (i : Fin m) → Fin (len i) → ZMod 2)) k) =
          ∏ k ∈ ({i} : Finset (Fin m))ᶜ,
            Function.update a i (fun w => if w = 0 then 1 else 0) k (x k) := by
        refine Finset.prod_congr rfl fun k hk => ?_
        have hki : k ≠ i := by simpa using hk
        rw [Function.update_of_ne hki, Pi.add_apply, Pi.single_eq_of_ne hki, add_zero]
      rw [e3, Function.update_self, hx]
      simp
    · simp
  · have e1 : ¬ (x + (Pi.single i v : (i : Fin m) → Fin (len i) → ZMod 2)) i = v := by simpa using hx
    simp only [e1, ite_false]
    have : ∏ k, Function.update a i (fun w => if w = 0 then 1 else 0) k (x k) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hx])
    simp [this]

theorem dm_decomp {m s : ℕ} {len : Fin m → ℕ}
    (R : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ) (i : Fin m) (S : Finset (Fin s → ZMod 2))
    (c : Fin s → ZMod 2) :
    massAt R a S c = ∑ v : Fin (len i) → ZMod 2, a i v *
      massAt R (Function.update a i (fun w => if w = 0 then 1 else 0)) S (c + R (Pi.single i v)) := by
  rw [Finset.sum_congr rfl (fun v _ => dm_term R a i S c v), Finset.sum_comm]
  unfold massAt
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem dm_base {m s : ℕ} {len : Fin m → ℕ}
    (R : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ)
    (ha : ∀ i : Fin m, 0 ≤ i.val → ∀ v, v ≠ 0 → a i v = 0)
    (S : Finset (Fin s → ZMod 2)) (c : Fin s → ZMod 2) :
    massAt R a S c = if c ∈ S then ∏ i, a i 0 else 0 := by
  unfold massAt
  rw [Finset.sum_eq_single (0 : (i : Fin m) → Fin (len i) → ZMod 2)]
  · simp
  · intro x _ hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have : ∏ k, a k (x k) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (ha i (Nat.zero_le _) _ hi)
    simp [this]
  · simp

theorem dm_D0 {m s : ℕ} {len : Fin m → ℕ}
    (P Q : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (U : ℕ → Submodule (ZMod 2) (Fin s → ZMod 2))
    (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ)
    (ha : ∀ i : Fin m, 0 ≤ i.val → ∀ v, v ≠ 0 → a i v = 0)
    (S : Finset (Fin s → ZMod 2)) (c : Fin s → ZMod 2) :
    ∃ T : Finset (Fin s → ZMod 2), T.card ≤ (S.filter (fun y => y - c ∈ U 0)).card ∧
      massAt P a S c ≤ massAt Q a T 0 := by
  by_cases hc : c ∈ S
  · refine ⟨{0}, ?_, ?_⟩
    · rw [Finset.card_singleton]
      exact Finset.card_pos.mpr ⟨c, by simp [hc]⟩
    · rw [dm_base P a ha, dm_base Q a ha]
      simp [hc]
  · refine ⟨∅, by simp, ?_⟩
    rw [dm_base P a ha]
    simp [hc]

theorem dm_step {m s : ℕ} {len : Fin m → ℕ}
    (P Q : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (U : ℕ → Submodule (ZMod 2) (Fin s → ZMod 2))
    (hmono : ∀ j, U j ≤ U (j+1))
    (hQs : ∀ (i : Fin m) (v : Fin (len i) → ZMod 2), Q (Pi.single i v) ∈ U (i.val+1))
    (h2 : ∀ (i : Fin m) (v : Fin (len i) → ZMod 2), P (Pi.single i v) - Q (Pi.single i v) ∈ U i.val)
    (h3 : ∀ (i : Fin m) (v : Fin (len i) → ZMod 2), Q (Pi.single i v) ∈ U i.val → Q (Pi.single i v) = 0)
    (j : ℕ) (hj : j < m)
    (ih : ∀ a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ,
      (∀ i : Fin m, j ≤ i.val → ∀ v, v ≠ 0 → a i v = 0) →
      ∀ (S : Finset (Fin s → ZMod 2)) (c : Fin s → ZMod 2),
      ∃ T : Finset (Fin s → ZMod 2), T.card ≤ (S.filter (fun y => y - c ∈ U j)).card ∧
        massAt P a S c ≤ massAt Q a T 0)
    (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ)
    (ha : ∀ i : Fin m, j + 1 ≤ i.val → ∀ v, v ≠ 0 → a i v = 0)
    (S : Finset (Fin s → ZMod 2)) (c : Fin s → ZMod 2) :
    ∃ T : Finset (Fin s → ZMod 2), T.card ≤ (S.filter (fun y => y - c ∈ U (j+1))).card ∧
      massAt P a S c ≤ massAt Q a T 0 := by
  set i : Fin m := ⟨j, hj⟩ with hi
  set a' := Function.update a i (fun w => if w = 0 then 1 else 0) with ha'
  have ha'sh : ∀ k : Fin m, j ≤ k.val → ∀ v, v ≠ 0 → a' k v = 0 := by
    intro k hk v hv
    by_cases hki : k = i
    · subst hki
      simp [ha', hv]
    · rw [ha', Function.update_of_ne hki]
      have : k.val ≠ j := fun h => hki (Fin.ext h)
      exact ha k (by omega) v hv
  choose B hBc hBmax using dm_best (fun T : Finset (Fin s → ZMod 2) => massAt Q a' T 0)
  set Sw : (Fin s → ZMod 2) → Finset (Fin s → ZMod 2) :=
    fun w => S.filter (fun y => y - c - w ∈ U j) with hSw
  set L := (Finset.univ : Finset (Fin (len i) → ZMod 2)).image (fun v => Q (Pi.single i v)) with hL
  refine ⟨L.biUnion (fun w => (B (Sw w).card).image (fun t => t + w)), ?_, ?_⟩
  · have hdisj : (L : Set (Fin s → ZMod 2)).PairwiseDisjoint Sw := by
      intro w hw w' hw' hne
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
      obtain ⟨v', _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw')
      refine Finset.disjoint_left.mpr fun y hy hy' => hne ?_
      have h1 := (Finset.mem_filter.mp hy).2
      have h1' := (Finset.mem_filter.mp hy').2
      have hd : Q (Pi.single i (v - v')) ∈ U i.val := by
        rw [Pi.single_sub, map_sub]
        have e : Q (Pi.single i v) - Q (Pi.single i v') =
            (y - c - Q (Pi.single i v')) - (y - c - Q (Pi.single i v)) := by abel
        rw [e]
        exact Submodule.sub_mem _ h1' h1
      have h4 := h3 i _ hd
      rw [Pi.single_sub, map_sub, sub_eq_zero] at h4
      exact h4
    have hsub : L.biUnion Sw ⊆ S.filter (fun y => y - c ∈ U (j+1)) := by
      intro y hy
      obtain ⟨w, hw, hy⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hyS, hyU⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨hyS, ?_⟩
      have e : y - c = (y - c - Q (Pi.single i v)) + Q (Pi.single i v) := by abel
      rw [e]
      exact Submodule.add_mem _ (hmono j hyU) (hQs i v)
    calc _ ≤ ∑ w ∈ L, ((B (Sw w).card).image (fun t => t + w)).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ L, (Sw w).card := Finset.sum_le_sum fun w _ => Finset.card_image_le.trans (hBc _)
      _ = (L.biUnion Sw).card := (Finset.card_biUnion hdisj).symm
      _ ≤ _ := Finset.card_le_card hsub
  · rw [dm_decomp P a i S c, dm_decomp Q a i _ 0]
    refine Finset.sum_le_sum fun v _ => Nat.mul_le_mul_left _ ?_
    obtain ⟨Tv, hTc, hTm⟩ := ih a' ha'sh S (c + P (Pi.single i v))
    have hf : S.filter (fun y => y - (c + P (Pi.single i v)) ∈ U j) = Sw (Q (Pi.single i v)) := by
      refine Finset.filter_congr fun y _ => ?_
      have e : y - c - Q (Pi.single i v) =
          (y - (c + P (Pi.single i v))) + (P (Pi.single i v) - Q (Pi.single i v)) := by abel
      rw [e, Submodule.add_mem_iff_left _ (h2 i v)]
    rw [hf] at hTc
    refine hTm.trans ((hBmax _ Tv hTc).trans (dm_mono Q a' _ _ 0 _ fun y hy => ?_))
    rw [add_zero] at hy
    rw [zero_add]
    exact Finset.mem_biUnion.mpr ⟨Q (Pi.single i v), Finset.mem_image_of_mem _ (Finset.mem_univ v),
      Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩

theorem dm_D {m s : ℕ} {len : Fin m → ℕ}
    (P Q : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (U : ℕ → Submodule (ZMod 2) (Fin s → ZMod 2))
    (hmono : ∀ j, U j ≤ U (j+1))
    (hQs : ∀ (i : Fin m) (v : Fin (len i) → ZMod 2), Q (Pi.single i v) ∈ U (i.val+1))
    (h2 : ∀ (i : Fin m) (v : Fin (len i) → ZMod 2), P (Pi.single i v) - Q (Pi.single i v) ∈ U i.val)
    (h3 : ∀ (i : Fin m) (v : Fin (len i) → ZMod 2), Q (Pi.single i v) ∈ U i.val → Q (Pi.single i v) = 0)
    (j : ℕ) : j ≤ m → ∀ a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ,
      (∀ i : Fin m, j ≤ i.val → ∀ v, v ≠ 0 → a i v = 0) →
      ∀ (S : Finset (Fin s → ZMod 2)) (c : Fin s → ZMod 2),
      ∃ T : Finset (Fin s → ZMod 2), T.card ≤ (S.filter (fun y => y - c ∈ U j)).card ∧
        massAt P a S c ≤ massAt Q a T 0 := by
  induction j with
  | zero => exact fun _ a ha S c => dm_D0 P Q U a ha S c
  | succ j ih =>
    intro hj
    exact dm_step P Q U hmono hQs h2 h3 j (by omega) (ih (by omega))

theorem dom {m s : ℕ} {len : Fin m → ℕ}
    (P Q : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (U : ℕ → Submodule (ZMod 2) (Fin s → ZMod 2))
    (hmono : ∀ j, U j ≤ U (j+1))
    (hP0 : ∀ j, ∀ x ∈ Pre m len j, P x ∈ U j)
    (hQs : ∀ (i : Fin m) (v : Fin (len i) → ZMod 2), Q (Pi.single i v) ∈ U (i.val+1))
    (h2 : ∀ (i : Fin m) (v : Fin (len i) → ZMod 2), P (Pi.single i v) - Q (Pi.single i v) ∈ U i.val)
    (h3 : ∀ (i : Fin m) (v : Fin (len i) → ZMod 2), Q (Pi.single i v) ∈ U i.val → Q (Pi.single i v) = 0)
    (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ) (S : Finset (Fin s → ZMod 2)) :
    ∃ T : Finset (Fin s → ZMod 2), T.card = S.card ∧ massAt P a S 0 ≤ massAt Q a T 0 := by
  obtain ⟨T0, hc, hm⟩ := dm_D P Q U hmono hQs h2 h3 m le_rfl a
    (fun i hi => absurd i.isLt (by omega)) S 0
  obtain ⟨T, hT, hTc⟩ := Finset.exists_superset_card_eq
    (hc.trans (Finset.card_filter_le _ _)) (Finset.card_le_univ S)
  exact ⟨T, hTc, hm.trans (dm_mono Q a T0 T 0 0 fun y hy => hT hy)⟩

theorem cn_proj_sub {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {p q : Submodule (ZMod 2) E}
    (h : IsCompl p q) (y : E) : y - p.projection q h y ∈ q := by
  rw [show y - p.projection q h y = q.projection p h.symm y from by
    rw [sub_eq_iff_eq_add']; exact (Submodule.projection_add_projection_eq_self h y).symm]
  exact Submodule.projection_apply_mem _ _

theorem cn_proj_zero {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {p q : Submodule (ZMod 2) E}
    (h : IsCompl p q) (y : E) (hy : p.projection q h y ∈ q) : p.projection q h y = 0 :=
  (Submodule.disjoint_def.mp h.disjoint) _ (Submodule.projection_apply_mem h y) hy

noncomputable def cn_C {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) (i : Fin m) :
    Submodule (ZMod 2) (Fin s → ZMod 2) :=
  Classical.choose (Submodule.exists_isCompl ((Pre m len i.val).map P))

theorem cn_hC {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) (i : Fin m) :
    IsCompl ((Pre m len i.val).map P) (cn_C P i) :=
  Classical.choose_spec (Submodule.exists_isCompl ((Pre m len i.val).map P))

noncomputable def cn_pi {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) (i : Fin m) :
    (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) :=
  (cn_C P i).projection _ (cn_hC P i).symm

noncomputable def cn_Q {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) :
    ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) :=
  ∑ i : Fin m, cn_pi P i ∘ₗ P ∘ₗ LinearMap.single (ZMod 2) (fun i => Fin (len i) → ZMod 2) i ∘ₗ
    LinearMap.proj i

theorem cn_Q_apply {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (x : (i : Fin m) → Fin (len i) → ZMod 2) :
    cn_Q P x = ∑ i : Fin m, cn_pi P i (P (Pi.single i (x i))) := by
  simp [cn_Q, LinearMap.sum_apply]

theorem cn_Q_single {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (i : Fin m) (v : Fin (len i) → ZMod 2) :
    cn_Q P (Pi.single i v) = cn_pi P i (P (Pi.single i v)) := by
  rw [cn_Q_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem cn_single_mem {m : ℕ} {len : Fin m → ℕ} (i : Fin m) (v : Fin (len i) → ZMod 2) :
    Pi.single (M := fun i => Fin (len i) → ZMod 2) i v ∈ Pre m len (i.val + 1) := by
  intro k hk
  have : k ≠ i := by
    rintro rfl
    omega
  simp [Pi.single_eq_of_ne this]

theorem cn_Pre_mono {m : ℕ} {len : Fin m → ℕ} {a b : ℕ} (h : a ≤ b) :
    Pre m len a ≤ Pre m len b :=
  fun _ hx k hk => hx k (le_trans h hk)

theorem cn_U_mono {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) {a b : ℕ} (h : a ≤ b) :
    (Pre m len a).map P ≤ (Pre m len b).map P :=
  Submodule.map_mono (cn_Pre_mono h)

theorem cn_h5 {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (i : Fin m) (v : Fin (len i) → ZMod 2) :
    P (Pi.single i v) - cn_Q P (Pi.single i v) ∈ (Pre m len i.val).map P := by
  rw [cn_Q_single]
  exact cn_proj_sub (cn_hC P i).symm _

theorem cn_h6 {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (i : Fin m) (v : Fin (len i) → ZMod 2)
    (h : cn_Q P (Pi.single i v) ∈ (Pre m len i.val).map P) : cn_Q P (Pi.single i v) = 0 := by
  rw [cn_Q_single] at *
  exact cn_proj_zero _ _ h

theorem cn_h4 {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (i : Fin m) (v : Fin (len i) → ZMod 2) :
    cn_Q P (Pi.single i v) ∈ (Pre m len (i.val + 1)).map P := by
  rw [← sub_sub_cancel (P (Pi.single i v)) (cn_Q P (Pi.single i v))]
  exact Submodule.sub_mem _ (Submodule.mem_map_of_mem (cn_single_mem i v))
    (cn_U_mono P (Nat.le_succ _) (cn_h5 P i v))

theorem cn_le {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) (j : ℕ) :
    (Pre m len j).map (cn_Q P) ≤ (Pre m len j).map P := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap, ← Finset.univ_sum_single x, map_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases hij : j ≤ i.val
  · rw [hx i hij, Pi.single_zero, map_zero]
    exact Submodule.zero_mem _
  · exact cn_U_mono P (by omega) (cn_h4 P i (x i))

theorem cn_ge {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) (j : ℕ) :
    ∀ y ∈ (Pre m len j).map P, ∃ x ∈ Pre m len j, cn_Q P x = y := by
  induction j with
  | zero =>
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    have : x = 0 := funext fun i => hx i (Nat.zero_le _)
    exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
  | succ j ih =>
    intro y hy
    by_cases hj : j < m
    · obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      set i : Fin m := ⟨j, hj⟩ with hi
      set x0 := Function.update x i 0 with hx0d
      set sv := Pi.single (M := fun i => Fin (len i) → ZMod 2) i (x i) with hsv
      have hx0 : x0 ∈ Pre m len j := by
        intro k hk
        by_cases hki : k = i
        · subst hki
          simp [hx0d]
        · rw [hx0d, Function.update_of_ne hki]
          exact hx k (by
            have : k.val ≠ j := fun h => hki (Fin.ext h)
            omega)
      have hsplit : x = x0 + sv := by
        funext k
        by_cases hki : k = i
        · subst hki
          simp [hx0d, hsv]
        · simp [hx0d, hsv, Function.update_of_ne hki, Pi.single_eq_of_ne hki]
      have hPx : P x = P x0 + P sv := by rw [← map_add, ← hsplit]
      have hmem : P x - cn_Q P sv ∈ (Pre m len j).map P := by
        rw [hPx, add_sub_assoc]
        exact Submodule.add_mem _ (Submodule.mem_map_of_mem hx0) (cn_h5 P i (x i))
      obtain ⟨x'', hx'', hq⟩ := ih _ hmem
      refine ⟨x'' + sv, Submodule.add_mem _ (cn_Pre_mono (Nat.le_succ j) hx'') (cn_single_mem i (x i)), ?_⟩
      rw [map_add, hq, sub_add_cancel]
    · have hle : Pre m len (j + 1) ≤ Pre m len j := fun x _ k hk => absurd hk (by
        have := k.isLt
        omega)
      obtain ⟨x, hx, hq⟩ := ih y (Submodule.map_mono hle hy)
      exact ⟨x, cn_Pre_mono (Nat.le_succ j) hx, hq⟩

theorem cn_h2 {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) (j : ℕ) :
    (Pre m len j).map (cn_Q P) = (Pre m len j).map P := by
  refine le_antisymm (cn_le P j) (fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := cn_ge P j y hy
  exact Submodule.mem_map_of_mem hx

theorem cn_mem_Pre_m {m : ℕ} {len : Fin m → ℕ} (x : (i : Fin m) → Fin (len i) → ZMod 2) :
    x ∈ Pre m len m := fun k hk => absurd hk (by
  have := k.isLt
  omega)

theorem cn_h1 {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (hP : Function.Surjective P) : Function.Surjective (cn_Q P) := by
  intro y
  obtain ⟨x, rfl⟩ := hP y
  have h : P x ∈ (Pre m len m).map (cn_Q P) := by
    rw [cn_h2]
    exact Submodule.mem_map_of_mem (cn_mem_Pre_m x)
  obtain ⟨x', _, h'⟩ := Submodule.mem_map.mp h
  exact ⟨x', h'⟩

theorem cn_h3_aux {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (w : Fin m → Fin s → ZMod 2) (hw4 : ∀ i, w i ∈ (Pre m len (i.val + 1)).map P)
    (hw6 : ∀ i, w i ∈ (Pre m len i.val).map P → w i = 0) (j : ℕ) :
    j ≤ m → (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < j), w i = 0) →
      ∀ i : Fin m, i.val < j → w i = 0 := by
  induction j with
  | zero =>
    intro _ _ i hi
    omega
  | succ j ih =>
    intro hj hsum i hi
    set i0 : Fin m := ⟨j, by omega⟩ with hi0
    have hfil : Finset.univ.filter (fun i : Fin m => i.val < j + 1) =
        insert i0 (Finset.univ.filter (fun i : Fin m => i.val < j)) := by
      ext k
      simp [hi0, Fin.ext_iff]
      omega
    rw [hfil, Finset.sum_insert (by simp [hi0])] at hsum
    have hS : ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < j), w i ∈ (Pre m len j).map P := by
      apply Submodule.sum_mem
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact cn_U_mono P (by omega) (hw4 k)
    have hw0 : w i0 = 0 := by
      apply hw6
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact Submodule.neg_mem _ hS
    rw [hw0, zero_add] at hsum
    by_cases hij : i.val < j
    · exact ih (by omega) hsum i hij
    · have : i = i0 := Fin.ext (by simp [hi0]; omega)
      rw [this, hw0]

theorem con {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (hP : Function.Surjective P) :
    ∃ Q : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2),
      Function.Surjective Q ∧
      (∀ j, (Pre m len j).map Q = (Pre m len j).map P) ∧
      (∀ x, Q x = 0 → ∀ i : Fin m, Q (Pi.single i (x i)) = 0) ∧
      (∀ (i : Fin m) (v : Fin (len i) → ZMod 2), Q (Pi.single i v) ∈ (Pre m len (i.val+1)).map P) ∧
      (∀ (i : Fin m) (v : Fin (len i) → ZMod 2),
        P (Pi.single i v) - Q (Pi.single i v) ∈ (Pre m len i.val).map P) ∧
      (∀ (i : Fin m) (v : Fin (len i) → ZMod 2),
        Q (Pi.single i v) ∈ (Pre m len i.val).map P → Q (Pi.single i v) = 0) := by
  refine ⟨cn_Q P, cn_h1 P hP, cn_h2 P, ?_, cn_h4 P, cn_h5 P, cn_h6 P⟩
  intro x hx i
  refine cn_h3_aux P (fun i => cn_Q P (Pi.single i (x i))) (fun i => cn_h4 P i (x i))
    (fun i => cn_h6 P i (x i)) m le_rfl ?_ i i.isLt
  rw [Finset.filter_true_of_mem (fun i _ => i.isLt), ← map_sum, Finset.univ_sum_single]
  exact hx

theorem pre_mono {m : ℕ} {len : Fin m → ℕ} (j : ℕ) : Pre m len j ≤ Pre m len (j+1) := by
  intro x hx i hi
  exact hx i (by omega)

theorem pref_eq {m s : ℕ} {len : Fin m → ℕ}
    (P : ((i : Fin m) → Fin (len i) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) (j : ℕ) :
    {y : Fin s → ZMod 2 | ∃ x : ((i : Fin m) → Fin (len i) → ZMod 2),
      (∀ i : Fin m, j ≤ i.val → x i = 0) ∧ P x = y} = ((Pre m len j).map P : Set (Fin s → ZMod 2)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.mem_map_of_mem hx
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end PEqualNP.Outside.L_lib_869_aux

theorem PEqualNP.Outside.L_lib_869 : (∀ (m s : Nat) (len : Fin m → Nat),
  let F := ZMod 2
  let V := fun i : Fin m => Fin (len i) → F
  let X := (i : Fin m) → V i
  let Y := Fin s → F
  let mass := fun (P : X →ₗ[F] Y) (a : (i : Fin m) → V i → Nat) (S : Finset Y) =>
    ∑ x : X, if P x ∈ S then ∏ i : Fin m, a i (x i) else 0
  let pref := fun (P : X →ₗ[F] Y) (j : Nat) =>
    {y : Y | ∃ x : X, (∀ i : Fin m, j ≤ i.val → x i = 0) ∧ P x = y}
  ∀ P : X →ₗ[F] Y, Function.Surjective P →
    ∃ Q : X →ₗ[F] Y, Function.Surjective Q ∧
      (∀ j : Nat, pref Q j = pref P j) ∧
      (∀ x : X, Q x = 0 → ∀ i : Fin m, Q (Pi.single i (x i)) = 0) ∧
      ∀ (a : (i : Fin m) → V i → Nat) (S : Finset Y), ∃ T : Finset Y,
        T.card = S.card ∧ mass P a S ≤ mass Q a T) := by
  intro m s len
  dsimp only
  intro P hP
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6⟩ := PEqualNP.Outside.L_lib_869_aux.con P hP
  refine ⟨Q, hQ1, fun j => ?_, hQ3, fun a S => ?_⟩
  · rw [PEqualNP.Outside.L_lib_869_aux.pref_eq, PEqualNP.Outside.L_lib_869_aux.pref_eq, hQ2 j]
  · obtain ⟨T, hT1, hT2⟩ := PEqualNP.Outside.L_lib_869_aux.dom P Q
      (fun j => (PEqualNP.Outside.L_lib_869_aux.Pre m len j).map P)
      (fun j => Submodule.map_mono (PEqualNP.Outside.L_lib_869_aux.pre_mono j))
      (fun j x hx => Submodule.mem_map_of_mem hx) hQ4 hQ5 hQ6 a S
    refine ⟨T, hT1, ?_⟩
    simpa only [PEqualNP.Outside.L_lib_869_aux.massAt, add_zero] using hT2
