import MyProject.Integral.Def

noncomputable section

open Real Classical

-- 積分の線形性

-- 極限の線形性を使いたい

theorem additive_integral (f g : Real → Real) (a b : Real) :
  Integral (fun t ↦ f t + g t) a b = Integral f a b + Integral g a b := by
  rw [← IsIntegral_iff]
  have hf : IsIntegral f a b (Integral f a b) := by rw [IsIntegral_iff]
  have hg : IsIntegral g a b (Integral g a b) := by rw [IsIntegral_iff]
  intro ε hε
  have hε2 : ε / 2 > 0 := by apply pos_half; exact hε
  rcases hf (ε / 2) hε2 with ⟨δf, hδf⟩
  rcases hg (ε / 2) hε2 with ⟨δg, hδg⟩
  apply Exists.intro (min δf δg)
  constructor
  · apply min_pos; exact hδf.1; exact hδg.1
  · intros n Δ ξ h h'
    rw [additive_riemann_sum]
    rw [add_sub_add]
    have hf' := hδf.2 n Δ ξ h (lt_le_trans _ _ _ h' (min_left_le δf δg))
    have hg' := hδg.2 n Δ ξ h (lt_le_trans _ _ _ h' (min_right_le δf δg))
    apply le_lt_trans
    apply abs_triangle
    rw [← half_add ε]
    apply lt_add_lt
    exact hf'
    exact hg'

theorem neg_integral (f : Real → Real) (a b : Real) :
  Integral (fun t ↦ -f t) a b = -Integral f a b := by
  rw [← IsIntegral_iff]
  have : IsIntegral f a b (Integral f a b) := by rw [IsIntegral_iff]
  intro ε hε
  rcases this ε hε with ⟨δ, hδ⟩
  apply Exists.intro δ
  constructor
  · exact hδ.1
  · intro n Δ ξ h h'
    rw [neg_riemann_sum]
    rw [neg_sub_neg_abs]
    exact hδ.2 n Δ ξ h h'

theorem sub_integral (f g : Real → Real) (a b : Real) :
  Integral (fun t ↦ f t - g t) a b = Integral f a b - Integral g a b := by
  rw [← add_neg_sub]
  rw [← neg_integral]
  rw [← additive_integral]
  apply integral_congr
  intro x
  rw [add_neg_sub]

theorem add_integrable (f g : Real → Real) (a b : Real)
    (hf : IsIntegrable f a b)
    (hg : IsIntegrable g a b) :
    IsIntegrable (fun x ↦ f x + g x) a b := by
  sorry

theorem neg_integrable (f : Real → Real) (a b : Real) (h : a ≤ b)
    (h'' : IsIntegrable f a b) : IsIntegrable (fun x ↦ -(f x)) a b := by
  sorry

theorem integrable_sub (f g : Real → Real) (a b : Real)
    (hf : IsIntegrable f a b)
    (hg : IsIntegrable g a b) :
    IsIntegrable (fun x ↦ f x - g x) a b := by
  sorry

theorem abs_integrable (f : Real → Real) (a b : Real) (h : a ≤ b)
    (h'' : IsIntegrable f a b) : IsIntegrable (fun x ↦ abs (f x)) a b := by
  sorry
