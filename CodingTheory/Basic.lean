import Mathlib

---- LINEAR CODE BASIC ----
variable(i j: Type)

/-- definition of linear code -/
abbrev LinearCode := Subspace (ZMod 2) (i → ZMod 2)

example [Fintype i] (C : LinearCode i) (x y : i → ZMod 2) (hx : x ∈ C) (hy : y ∈ C) : ℕ :=
hammingDist x y

/-- the set of indices (i) where v i ≠ 0 -/
def support [Fintype i] (v : i → ZMod 2) : Finset i := Finset.filter (fun i => v i ≠ 0) Finset.univ

/-- lemma: hamming norm = |support v| -/
lemma hammingNorm_eq_card_support [Fintype i] (v : i → ZMod 2)  :
  hammingNorm v = (support i v).card := by
  rw [hammingNorm, support]
/-- lemma: |support v| = hamming norm -/
lemma card_support_eq_hammingNorm [Fintype i] (v : i → ZMod 2) :
  (support i v).card = hammingNorm v := by
  exact hammingNorm_eq_card_support i v


---- DUAL CODE ----
/-- bilinear form under ZMod 2 for dual construction -/
def bilinForm_inner (ι : Type*) [Fintype ι] :
    LinearMap.BilinForm (ZMod 2) (ι → ZMod 2) where
  toFun f := {
    toFun g := ∑ i, f i * g i
    map_add' := by
      intros f₁ f₂
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intros r f
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum,RingHom.id_apply]
      congr! 1 with i
      rw [←mul_assoc, ←mul_assoc, mul_comm r, mul_assoc]
  }
  map_add' := by
    intros f₁ f₂
    ext g
    simp only [LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [←Finset.sum_add_distrib]
    congr! 1 with i
    ring

  map_smul' := by
    intros r f
    ext g
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
              RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk,
              LinearMap.smul_apply, smul_eq_mul]
    congr! 1 with i
    ring

/-- dual coade for linear code C: C⊥ = {x ∈ 𝔽₂ⁿ | x ⬝ y = 0  ∀ y ∈ C } -/
def dual [Fintype i] (c: LinearCode i): LinearCode i :=
  LinearMap.BilinForm.orthogonal (bilinForm_inner i) c


---- PARITY CHECK MATRIX ----
/-- parity-check matrix H for C: columns of H form a basis for dual code of C-/
def IsParityCheck [Fintype i] [Fintype j] [DecidableEq j]
  (H: Matrix i j (ZMod 2)) (C: LinearCode i): Prop :=
   (Submodule.span (ZMod 2) (Set.range H.toLin'.toFun) = dual i C) ∧
   LinearIndependent (ZMod 2) (fun j => (fun i => H i j) : j → (i → ZMod 2))

-- lemma: if x in ZMod 2 and x ≠ 0, then x = 1
lemma ZMod_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  { contradiction }
  { rfl }

-- lemma: if v is a word, then vH is a linear combination of exactly wt(v) rows of H
lemma vecMul_linear_comb [Fintype i] (v : i → ZMod 2) (H : Matrix i j (ZMod 2)) :
  Matrix.vecMul v H = ∑ i in support i v, v i • H i := by
  ext j
  simp only [Matrix.vecMul, dotProduct]
  rw[support]
  rw [Finset.sum_filter]
  simp only [ne_eq, ite_not, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro hi hFin
  split
  { -- case: `v hi = 0`
    have hvi: v hi = 0 := by assumption
    simp only [Pi.zero_apply, mul_eq_zero]
    exact mul_eq_mul_left_iff.mp (congrArg (HMul.hMul (H hi j)) hvi)
  }
  { -- case: `v hi ≠ 0` ie.  `v hi = 1`
    have hv_nonzero : (v hi) ≠ 0 := by assumption
    have hvi : v hi = 1 := ZMod_eq_one_of_ne_zero (v hi) hv_nonzero
    rw [hvi]
    simp only [one_mul]
    simp only [Pi.smul_apply, smul_eq_mul, one_mul]
  }

-- helper lemma: map mulVec to row
lemma exists_vec_mul_eq_column [Fintype j][DecidableEq j] (H : Matrix i j (ZMod 2)) (k : j) :
  ∃ y : j → ZMod 2, H.mulVec y = fun i => H i k := by
  use fun j => if j = k then 1 else 0
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.mul_apply]
  rw [Finset.sum_eq_single k]
  simp only [↓reduceIte, mul_one]
  intro hj hb hjk
  split
  {contradiction}
  {simp}
  { intro hk
    split
    { exfalso
      exact hk (Finset.mem_univ k) }
    {simp} }

-- theorem: for all words in code C, vH = 0 if H is a parity-check matrix for C
--  (⚠️ missing backward proof)
theorem code_mul_parity_zero [Fintype i] [Fintype j][DecidableEq j]
  (H: Matrix i j (ZMod 2)) (C: LinearCode i) (hH: IsParityCheck i j H C)
  (v: i → ZMod 2) (hv: v ∈ C) : Matrix.vecMul v H = 0 := by
  have h_dual : Submodule.span (ZMod 2) (Set.range H.toLin'.toFun) = dual i C := hH.1
  have h_rows_dual : ∀ k, (fun i => H i k) ∈ dual i C := by
    intro k
    rw [←h_dual]
    apply Submodule.subset_span
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Set.mem_range, Matrix.toLin'_apply]
    apply exists_vec_mul_eq_column
  have h_ortho : ∀ w ∈ dual i C, bilinForm_inner i v w = 0 :=
    fun w hw => (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) v hv
  ext k
  specialize h_ortho (fun i => H i k) (h_rows_dual k)
  rw [bilinForm_inner] at h_ortho
  simp only [LinearMap.coe_mk, AddHom.coe_mk] at h_ortho
  simp only [Matrix.vecMul, dotProduct, Pi.mul_apply, Pi.zero_apply]
  apply h_ortho


---- HAMMINGCODE ----
/-- Hamming Code: -/
def IsHammingCode [Fintype i] (C: LinearCode i) (r: ℕ): Prop :=
  ∃ (H: Matrix i (Fin (2^r - 1)) (ZMod 2)),
  IsParityCheck i (Fin (2^r - 1)) H C

---- CODE DISTANCE----
open Classical

/-- the set of all non zero codewords (ie. v ∈ C) -/
noncomputable def nonzeroCodewords [Fintype i] (C : LinearCode i): Finset (i → ZMod 2) :=
  Finset.filter (fun x ↦ x ≠ 0) (Finset.filter (fun x ↦ x ∈ C) Finset.univ)

/-- distance of a linear code is the minimum weight of any nonzero codeword
  where weight of a codeword v: hamming distance between v and 0 -/
noncomputable def codeDistance [Fintype i] (C : LinearCode i) : ℕ :=
  if h : (nonzeroCodewords i C).Nonempty then
    Finset.min' (Finset.image (fun x => hammingDist x 0) (nonzeroCodewords i C)) (by simp [h])
  else 0

-- lemma: for any codeword `v ∈ C`, its weight is greater or equal to the codeDistance
lemma codeDist_spec [Fintype i] (C: LinearCode i)
  (v: i → ZMod 2) (hv: v ∈ C) (h_v_nonzero : v ≠ 0) :
  codeDistance i C ≤ hammingDist v 0 := by
  have h_nonempty : (nonzeroCodewords i C).Nonempty := by
    use v
    simp only [nonzeroCodewords, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ v, hv⟩, h_v_nonzero⟩
  simp only [codeDistance]
  rw [dif_pos h_nonempty]
  apply Finset.min'_le
  simp only [Finset.mem_image, Finset.mem_filter]
  use v
  apply And.intro
  { rw [nonzeroCodewords]
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv, h_v_nonzero⟩}
  {simp}


---- MAIN THOEREM ----
-- lemma: for a linear code C, ∃ v ∈ C such that wt(v) = distance(C)
lemma exists_codeword_of_min_weight [Fintype i] (C: LinearCode i) (d: ℕ)
  (hC: (nonzeroCodewords i C).Nonempty)
  (h_dist: codeDistance i C = d) :
  ∃ v : i → ZMod 2, v ∈ C ∧ v ≠ 0 ∧ hammingNorm v = d := by
  simp only [codeDistance] at h_dist
  rw [dif_pos hC] at h_dist
  have h_img_nonempty : (Finset.image hammingNorm (nonzeroCodewords i C)).Nonempty := by
    obtain ⟨w⟩ := hC
    have hw: w ∈ nonzeroCodewords i C := by assumption
    use hammingNorm w
    simp only [Finset.mem_image]
    use w
  let d_min := Finset.min' (Finset.image hammingNorm (nonzeroCodewords i C)) h_img_nonempty
  have hd_eq_d : d_min = d := h_dist
  have hd_min_mem : d_min ∈ Finset.image hammingNorm (nonzeroCodewords i C) :=
    Finset.min'_mem (Finset.image hammingNorm (nonzeroCodewords i C)) h_img_nonempty
  obtain ⟨v, hv_mem, hv_weight⟩ := Finset.mem_image.mp hd_min_mem
  rw [nonzeroCodewords] at hv_mem
  simp only [Finset.mem_filter] at hv_mem
  obtain ⟨hv_C, hv_nonzero⟩ := hv_mem
  rw [hd_eq_d] at hv_weight
  exact ⟨v, hv_C.2, hv_nonzero, hv_weight⟩

-- lemma: distance(C) = d →
-- ⬝ at least one set of d rows of H is linearly dependent
-- ⬝ this set is the support of v
lemma exists_dependent_rows [Fintype i] [Fintype j]
  (H : Matrix i j (ZMod 2)) (C : LinearCode i) (d: ℕ)
  (hH: IsParityCheck i j H C)(hd: d ≥ 1)
  (v : i → ZMod 2) (hv : v ∈ C) (h_wt: hammingNorm v = d):
  ∃ (S : Finset i) (hS_def : S = support i v),
  S.card = d ∧ ¬ LinearIndependent (ZMod 2) (fun s : S => H s) := by
  let S := support i v
  have hS_card : S.card = d := by apply h_wt
  use S, rfl
  rw [not_linearIndependent_iff]
  constructor
  {exact hS_card}
  { use Finset.univ
    let g : S → ZMod 2 := fun x ↦ 1
    use g
    simp only [one_smul, ne_eq, one_ne_zero,
      not_false_eq_true, and_self, Subtype.exists, exists_prop, and_true, g]
    rw [Finset.sum_coe_sort]
    constructor
    { unfold S
      have hnew: ∑ i ∈ support i v, H i = 0 := by
        have hvH0: Matrix.vecMul v H = 0 := code_mul_parity_zero i j H C hH v hv
        rw [vecMul_linear_comb i j v H] at hvH0
        have h : ∑ i ∈ support i v, v i • H i = ∑ i ∈ support i v, 1 • H i := by
          congr! 1 with i hi
          have hvi : v i = 1 := by
            unfold support at hi
            apply ZMod_eq_one_of_ne_zero
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            apply hi
          rw [hvi]
          simp only [one_smul]
        rw [hvH0] at h
        rw [h]
        simp only [one_smul]
      apply hnew }
    { simp only [Finset.univ_eq_attach, Finset.mem_attach, exists_prop, and_true]
      rw [← hS_card] at hd
      have hcard : S.card > 0 := hd
      apply Finset.Nonempty.exists_mem
      have hcard': 0 < Finset.card S := hcard
      rw[← Finset.card_pos]
      exact hcard' } }

-- unfinished lemma: if there's a set of d linearly dependent rows of H,
-- then there exist a codeword v ∈ C which support equals to the set of rows
lemma exists_vector_with_support [Fintype i] [Fintype j]
  (H : Matrix i j (ZMod 2)) (C : LinearCode i)
  (hH: IsParityCheck i j H C) (d: ℕ) (hC: (nonzeroCodewords i C).Nonempty)
  (S : Finset i) (hS_card : S.card = d) (hS_dep : ¬ LinearIndependent (ZMod 2) (fun s : S => H s)) :
  ∃ (v : i → ZMod 2) (hv: v ∈ C),  v ≠ 0 ∧ (support i v = S) := by
  obtain ⟨w, hw, hw_nonzero⟩ := Fintype.not_linearIndependent_iff.mp hS_dep

  let v := fun i => if hi : i ∈ S then w ⟨i, hi⟩ else 0

  have hv_in_C : v ∈ C := by
    have hvH : Matrix.vecMul v H = 0 := by
      rw [vecMul_linear_comb i j v H]
      sorry
    sorry -- missing reverse of code_mul_parity_zero

  have hv_nonzero : v ≠ 0 := by
    intro hzero
    obtain ⟨i, hi_nonzero⟩ := hw_nonzero
    have hvi : v i = 0 := by
      rw [hzero]
      simp only [Pi.zero_apply]
    unfold v at hvi
    rw [dif_pos i.prop] at hvi
    simp at hvi
    contradiction

  have hv_support : support i v = S := by
    ext i
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, ite_ne_right_iff]
    constructor
    { -- if `i ∈ support v`, then `i ∈ S`
      intro hi
      unfold v at hi
      split_ifs at hi with hiS
      {exact hiS}
      {simp at hi}
    }
    { -- if `i ∈ S`, then `i ∈ support v`
      intro hiS
      intro hzero
      obtain ⟨⟨j, hj⟩, hj_nonzero⟩ := hw_nonzero
      sorry -- missing proof here
    }
  exact ⟨v, hv_in_C, hv_nonzero, hv_support⟩

-- lemma: distance(C) = d → any set of d-1 rows of H is linearly independent
lemma rows_independent_for_d_minus_one (H : Matrix i j (ZMod 2))
  (C : LinearCode i) (d : ℕ) [Fintype i] [Fintype j]
  (hH: IsParityCheck i j H C) (hC: (nonzeroCodewords i C).Nonempty)
  (h_dist: codeDistance i C = d) (hd: d ≥ 1) :
  ∀ S : Finset i, S.card = d - 1 → LinearIndependent (ZMod 2) (fun s : S => H s) := by
  by_contra h_dep_exists
  push_neg at h_dep_exists
  obtain ⟨S, hS_card, hS_dep⟩ := h_dep_exists

  obtain ⟨v, hvC, hv_nonzero, hv_support⟩ :=
    exists_vector_with_support i j H C hH (d-1) hC S hS_card hS_dep

  have hv_wt : hammingNorm v = d - 1 := by rw [← card_support_eq_hammingNorm, hv_support, hS_card]

  have h_dist_contra := codeDist_spec i C v hvC hv_nonzero
  rw [h_dist, hammingDist_zero_right] at h_dist_contra
  have hsimp: d-1 < d := by
    norm_num
    apply hd
  rw [← hv_wt] at hsimp
  linarith


-- main thoerem:
theorem distanceCriterion [Fintype i] [Fintype j]
  (H: Matrix i j (ZMod 2)) (C: LinearCode i) (d: ℕ) (hd: d ≥ 1)
  (hH: IsParityCheck i j H C) (hC: (nonzeroCodewords i C).Nonempty):
  codeDistance i C = d →
  (∀ S : Finset i, S.card = d - 1 → LinearIndependent (ZMod 2) (fun s : S => H s)) ∧
  (∃ S : Finset i, S.card = d ∧ ¬ LinearIndependent (ZMod 2) (fun s : S => H s)) := by
  intro h_dist
  obtain ⟨v, hvC, hv_nonzero, hv_wt⟩ := exists_codeword_of_min_weight i C d hC h_dist

  -- proof of linear dependency
  have hS_dep' : ∃ (S : Finset i) (hS_def : S = support i v),
    S.card = d ∧ ¬ LinearIndependent (ZMod 2) (fun s : S => H s) :=
      exists_dependent_rows i j H C d hH hd v hvC hv_wt
  obtain ⟨S,hS, hS_card, hS_dep⟩ := hS_dep'

  -- proof of linear independency
  have h_indep : ∀ S : Finset i,
    S.card = d - 1 → LinearIndependent (ZMod 2) (fun s : S => H s) := by
    intro S hS
    exact rows_independent_for_d_minus_one i j H C d hH hC h_dist hd S hS

  exact ⟨h_indep, ⟨S, hS_card, hS_dep⟩⟩
